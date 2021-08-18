module Dim.DiskBack where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Exception
import Data.Dynamic
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.Text as T
import Dim.Column
import Dim.DataType
import Dim.DbArray
import Dim.InMem
import Dim.XCHG
import Foreign hiding (void)
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.EHI
import Type.Reflection
import Prelude

data DbColumn a = (Eq a, Storable a, EdhXchg a, Typeable a) =>
  DbColumn
  { db'column'array :: !(DbArray a),
    db'column'offset :: !Int
  }

instance
  (Eq a, Storable a, EdhXchg a, Typeable a) =>
  ManagedColumn DbColumn DeviceArray a
  where
  view'column'data (DbColumn !dba !dbc'offs) !exit !ets =
    readTMVar (db'array'store dba) >>= \case
      Left !err -> throwSTM err
      Right (_shape, !hdr, !dbcs) -> do
        !dba'len <- fromIntegral <$> unsafeIOToSTM (readDbArrayLength hdr)
        exitEdh
          ets
          exit
          ( unsafeSliceDeviceArray dbcs dbc'offs $
              deviceArrayCapacity dbcs - dbc'offs,
            dba'len - dbc'offs
          )

  read'column'length (DbColumn !dba !dbc'offs) !exit !ets =
    readTMVar (db'array'store dba) >>= \case
      Left !err -> throwSTM err
      Right (_shape, !hdr, _dbcs) -> do
        !dba'len <- fromIntegral <$> unsafeIOToSTM (readDbArrayLength hdr)
        exitEdh ets exit $ dba'len - dbc'offs

  grow'column'capacity (DbColumn !dba !dbc'offs) !newCap !exit !ets =
    runEdhTx ets $
      edhContIO $
        bracket
          (atomically $ takeTMVar dbas)
          (atomically . tryPutTMVar dbas)
          $ const doIt
    where
      !dbas = db'array'store dba
      doIt = do
        mmapDbArray
          dbas
          (db'array'dir dba)
          (db'array'path dba)
          (Just $ ArrayShape $ ("", newCap + dbc'offs) :| [])
        atomically $
          readTMVar dbas >>= \case
            Left !err -> throwSTM err
            Right (_shape, !hdr, !dbcs) -> do
              !dba'len <- fromIntegral <$> unsafeIOToSTM (readDbArrayLength hdr)
              exitEdh
                ets
                exit
                ( unsafeSliceDeviceArray dbcs dbc'offs $
                    deviceArrayCapacity dbcs - dbc'offs,
                  dba'len - dbc'offs
                )

  mark'column'length (DbColumn !dba !dbc'offs) !newLen !exit !ets =
    readTMVar (db'array'store dba) >>= \case
      Left !err -> throwSTM err
      Right (_shape, !hdr, !dbcs) -> do
        let !cap = deviceArrayCapacity dbcs
        if newLen' < 0 || newLen' > cap
          then
            throwEdh ets UsageError $
              "column length out of range: "
                <> T.pack (show newLen)
                <> " vs "
                <> T.pack (show $ cap - dbc'offs)
          else do
            unsafeIOToSTM $ writeDbArrayLength hdr $ fromIntegral newLen'
            exitEdh ets exit ()
    where
      !newLen' = newLen + dbc'offs

  view'column'slice (DbColumn !dba !dbc'offs) !start !stop !exit !ets =
    readTMVar (db'array'store dba) >>= \case
      Left !err -> throwSTM err
      Right (_shape, !hdr, DeviceArray _cap !fp0) -> do
        !dba'len <- fromIntegral <$> unsafeIOToSTM (readDbArrayLength hdr)
        let !cl = dba'len - dbc'offs
        if
            | stop > cl ->
              throwEdh ets UsageError $
                "column slice range out of range: "
                  <> T.pack (show start)
                  <> ":"
                  <> T.pack (show stop)
                  <> " vs "
                  <> T.pack (show dba'len)
            | stop == cl ->
              exitEdh
                ets
                exit
                ( StayComposed,
                  someColumn $ DbColumn dba $ dbc'offs + start
                )
            | otherwise -> do
              !csvNew <-
                newTMVar $
                  DeviceArray @a (stop - start) $
                    plusForeignPtr fp0 $
                      (dbc'offs + start) * sizeOf (undefined :: a)
              !clvNew <- newTVar $ stop - start
              exitEdh
                ets
                exit
                (ExtractAlone, someColumn $ InMemDevCol csvNew clvNew)

  copy'column'slice (DbColumn !dba !dbc'offs) !start !stop !step !exit !ets =
    readTMVar (db'array'store dba) >>= \case
      Left !err -> throwSTM err
      Right (_shape, !hdr, DeviceArray _cap (fp0 :: ForeignPtr a)) -> do
        !dba'len <- fromIntegral <$> unsafeIOToSTM (readDbArrayLength hdr)
        let fp :: ForeignPtr a =
              plusForeignPtr fp0 $ dbc'offs * sizeOf (undefined :: a)
            !cl = dba'len - dbc'offs
        if stop < start || start < 0 || stop > cl
          then
            throwEdh ets UsageError $
              "column slice range out of range: "
                <> T.pack (show start)
                <> ":"
                <> T.pack (show stop)
                <> " vs "
                <> T.pack (show cl)
          else runEdhTx ets $
            edhContIO $ do
              let (q, r) = quotRem (stop - start) step
                  !len = if r == 0 then abs q else 1 + abs q
              !cs' <-
                if len <= 0
                  then emptyDeviceArray
                  else (DeviceArray len <$>) $
                    withForeignPtr fp $ \ !p -> do
                      !p' <- callocArray len
                      !fp' <- newForeignPtr finalizerFree p'
                      let fillRng :: Int -> Int -> IO (ForeignPtr a)
                          fillRng !n !i =
                            if i >= len
                              then return fp'
                              else do
                                peekElemOff p n >>= pokeElemOff p' i
                                fillRng (n + step) (i + 1)
                      fillRng start 0
              atomically $ do
                !csvNew <- newTMVar cs'
                !clvNew <- newTVar len
                exitEdh
                  ets
                  exit
                  (ExtractAlone, someColumn $ InMemDevCol csvNew clvNew)

  derive'new'column (DbColumn !dba !dbc'offs) !sizer (!deriver, !exit) =
    atomically (readTMVar $ db'array'store dba) >>= \case
      Left !err -> throwIO err
      Right (_shape, !hdr, DeviceArray !cap (fp0 :: ForeignPtr a)) -> do
        let !cs =
              DeviceArray
                (cap - dbc'offs)
                (plusForeignPtr fp0 $ dbc'offs * sizeOf (undefined :: a))
        !cl <- subtract dbc'offs . fromIntegral <$> readDbArrayLength hdr

        let !cap' = sizer (cs, cl, deviceArrayCapacity cs)
        (_, !cs') <- newDeviceArray cap'
        !cl' <- deriver (cs, cl) (cs', cap')
        !csv' <- newTMVarIO cs'
        !clv' <- newTVarIO cl'
        exit $ InMemDevCol csv' clv'

  extract'column'bool (DbColumn !dba !dbc'offs) !idxCol !exit !ets =
    readTMVar (db'array'store dba) >>= \case
      Left !err -> throwSTM err
      Right (_shape, !hdr, DeviceArray _cap (fp0 :: ForeignPtr a)) ->
        runEdhTx ets $
          view'column'data idxCol $ \(!idxa, !idxl) -> edhContIO $ do
            let !fp = plusForeignPtr fp0 $ dbc'offs * sizeOf (undefined :: a)
            !cl <- subtract dbc'offs . fromIntegral <$> readDbArrayLength hdr
            if idxl /= cl
              then
                atomically $
                  throwEdh ets UsageError $
                    "bool index shape mismatch - "
                      <> T.pack (show idxl)
                      <> " vs "
                      <> T.pack (show cl)
              else do
                (!fp', !cl') <- withForeignPtr fp $ \ !p -> do
                  !p' <- callocArray cl
                  !fp' <- newForeignPtr finalizerFree p'
                  let extractAt :: Int -> Int -> IO (ForeignPtr a, Int)
                      extractAt !i !n =
                        if i >= cl
                          then return (fp', n)
                          else do
                            array'reader idxa i >>= \case
                              YesNo 0 -> extractAt (i + 1) n
                              _ -> do
                                peekElemOff p i >>= pokeElemOff p' n
                                extractAt (i + 1) (n + 1)
                  extractAt 0 0
                let !cs' = DeviceArray cl fp'
                atomically $ do
                  !csvNew <- newTMVar cs'
                  !clvNew <- newTVar cl'
                  exitEdh ets exit $ someColumn $ InMemDevCol csvNew clvNew

  extract'column'fancy (DbColumn !dba !dbc'offs) !idxCol !exit !ets =
    readTMVar (db'array'store dba) >>= \case
      Left !err -> throwSTM err
      Right (_shape, _hdr, DeviceArray _cap (fp0 :: ForeignPtr a)) ->
        runEdhTx ets $
          view'column'data idxCol $ \(!idxa, !idxl) -> edhContIO $ do
            let !fp = plusForeignPtr fp0 $ dbc'offs * sizeOf (undefined :: a)
            -- !cl <- subtract dbc'offs . fromIntegral <$> readDbArrayLength hdr
            !fp' <- withForeignPtr fp $ \ !p -> do
              !p' <- callocArray idxl
              !fp' <- newForeignPtr finalizerFree p'
              let extractAt :: Int -> IO (ForeignPtr a)
                  extractAt !i =
                    if i >= idxl
                      then return fp'
                      else do
                        !idxi <- array'reader idxa i
                        peekElemOff p idxi >>= pokeElemOff p' i
                        extractAt (i + 1)
              extractAt 0
            let !cs' = DeviceArray idxl fp'
            atomically $ do
              !csvNew <- newTMVar cs'
              !clvNew <- newTVar idxl
              exitEdh ets exit $ someColumn $ InMemDevCol csvNew clvNew

asDbColumnOf ::
  forall a r.
  (Typeable a) =>
  Object ->
  r ->
  (DbColumn a -> r) ->
  r
asDbColumnOf !obj !naExit !exit = case dynamicHostData obj of
  Nothing -> naExit
  Just (Dynamic trDBC dbc) ->
    case trDBC `eqTypeRep` typeRep @(DbColumn a) of
      Nothing -> naExit
      Just HRefl -> exit dbc

asDbColumnOf' ::
  forall a r.
  (Typeable a) =>
  EdhValue ->
  r ->
  (DbColumn a -> r) ->
  r
asDbColumnOf' !val !naExit !exit = case edhUltimate val of
  EdhObject !obj -> asDbColumnOf obj naExit exit
  _ -> naExit

withDbColumnOf ::
  forall a.
  Typeable a =>
  Object ->
  EdhTx ->
  (Object -> DbColumn a -> EdhTx) ->
  EdhTx
withDbColumnOf !obj naExit !dbcExit !ets = do
  supers <- readTVar $ edh'obj'supers obj
  withComposition $ obj : supers
  where
    withComposition :: [Object] -> STM ()
    withComposition [] = runEdhTx ets naExit
    withComposition (o : rest) =
      asDbColumnOf @a o (withComposition rest) (runEdhTx ets . dbcExit o)

withDbColumnOf' ::
  forall a.
  Typeable a =>
  EdhValue ->
  EdhTx ->
  (Object -> DbColumn a -> EdhTx) ->
  EdhTx
withDbColumnOf' !val naExit !dbcExit = case edhUltimate val of
  EdhObject !obj -> do
    withDbColumnOf obj naExit dbcExit
  _ -> naExit

withDbColumnSelfOf ::
  forall a.
  Typeable a =>
  (Object -> DbColumn a -> EdhTx) ->
  EdhTx
withDbColumnSelfOf !dbcExit !ets =
  runEdhTx ets $ withDbColumnOf @a that naExit dbcExit
  where
    that = edh'scope'that $ contextScope $ edh'context ets
    naExit =
      throwEdhTx UsageError $
        "not an expected self column of type " <> T.pack (show $ typeRep @a)

withDbColumnSelf ::
  (forall a. Object -> DbColumn a -> EdhTx) ->
  EdhTx
withDbColumnSelf !dbcExit !ets = do
  supers <- readTVar $ edh'obj'supers that
  withComposition $ that : supers
  where
    that = edh'scope'that $ contextScope $ edh'context ets
    naExit = throwEdh ets UsageError "not an expected self column"

    withComposition :: [Object] -> STM ()
    withComposition [] = naExit
    withComposition (o : rest) = case dynamicHostData o of
      Nothing -> withComposition rest
      Just (Dynamic trDBC dbc) -> case trDBC of
        App trDBCC _ -> case trDBCC `eqTypeRep` typeRep @DbColumn of
          Nothing -> withComposition rest
          Just HRefl -> runEdhTx ets $ dbcExit o dbc
        _ -> withComposition rest
