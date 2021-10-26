module Dim.DiskBack where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import Control.Monad.IO.Class
import Data.Dynamic
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.Text as T
import Dim.Column
import Dim.DbArray
import Dim.FlatArray
import Dim.InMem
import Event.Analytics.EHI
import Foreign hiding (void)
import Language.Edh.EHI
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
  view'column'data (DbColumn !dba !dbc'offs) =
    readTMVarEIO (db'array'store dba) >>= \case
      Left !err -> throwHostEIO err
      Right (_shape, !hdr, !dbcs) -> do
        !dba'len <- liftIO $ fromIntegral <$> readDbArrayLength hdr
        return
          ( unsafeSliceDeviceArray dbcs dbc'offs $
              deviceArrayCapacity dbcs - dbc'offs,
            dba'len - dbc'offs
          )

  read'column'length (DbColumn !dba !dbc'offs) =
    readTMVarEIO (db'array'store dba) >>= \case
      Left !err -> throwHostEIO err
      Right (_shape, !hdr, _dbcs) -> do
        !dba'len <- liftIO $ fromIntegral <$> readDbArrayLength hdr
        return $ dba'len - dbc'offs

  grow'column'capacity (DbColumn !dba !dbc'offs) !newCap =
    liftIO $
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
          False
        atomically (readTMVar dbas) >>= \case
          Left !err -> throwIO err
          Right (_shape, !hdr, !dbcs) -> do
            !dba'len <- fromIntegral <$> readDbArrayLength hdr
            return
              ( unsafeSliceDeviceArray dbcs dbc'offs $
                  deviceArrayCapacity dbcs - dbc'offs,
                dba'len - dbc'offs
              )

  mark'column'length (DbColumn !dba !dbc'offs) !newLen =
    readTMVarEIO (db'array'store dba) >>= \case
      Left !err -> throwHostEIO err
      Right (_shape, !hdr, !dbcs) -> do
        let !cap = deviceArrayCapacity dbcs
        if newLen' < 0 || newLen' > cap
          then
            throwEdhM
              UsageError
              $ T.pack $
                "column length out of range: " <> show newLen <> " vs "
                  <> show (cap - dbc'offs)
          else
            void $
              liftIO $ writeDbArrayLength hdr $ fromIntegral newLen'
    where
      !newLen' = newLen + dbc'offs

  view'column'slice (DbColumn !dba !dbc'offs) !start !stop =
    readTMVarEIO (db'array'store dba) >>= \case
      Left !err -> throwHostEIO err
      Right (_shape, !hdr, DeviceArray _cap !fp0) -> do
        !dba'len <- liftIO $ fromIntegral <$> readDbArrayLength hdr
        let !cl = dba'len - dbc'offs
        if
            | stop > cl ->
              throwEdhM
                UsageError
                $ T.pack $
                  "column slice range out of range: "
                    <> show start
                    <> ":"
                    <> show stop
                    <> " vs "
                    <> show dba'len
            | stop == cl ->
              return
                (StayComposed, someColumn $ DbColumn dba $ dbc'offs + start)
            | otherwise -> do
              !csvNew <-
                newTMVarEIO $
                  DeviceArray @a (stop - start) $
                    plusForeignPtr fp0 $
                      (dbc'offs + start) * sizeOf (undefined :: a)
              !clvNew <- newTVarEIO $ stop - start
              return (ExtractAlone, someColumn $ InMemDevCol csvNew clvNew)

  copy'column'slice
    (DbColumn !dba !dbc'offs)
    !ccap
    !start
    !stop
    !step =
      readTMVarEIO (db'array'store dba) >>= \case
        Left !err -> throwHostEIO err
        Right (_shape, !hdr, DeviceArray _cap (fp0 :: ForeignPtr a)) -> do
          !dba'len <- liftIO $ fromIntegral <$> readDbArrayLength hdr
          let fp :: ForeignPtr a =
                plusForeignPtr fp0 $ dbc'offs * sizeOf (undefined :: a)
              !cl = dba'len - dbc'offs
          if stop < start || start < 0 || stop > cl
            then
              throwEdhM
                UsageError
                $ T.pack $
                  "column slice range out of range: " <> show start <> ":"
                    <> show stop
                    <> " vs "
                    <> show cl
            else do
              let (q, r) = quotRem (stop - start) step
                  !len = if r == 0 then abs q else 1 + abs q
              if ccap < len
                then
                  throwEdhM
                    UsageError
                    $ T.pack $
                      "capacity too small: " <> show ccap <> " vs "
                        <> show start
                        <> ":"
                        <> show stop
                        <> ":"
                        <> show step
                else do
                  !cs' <- liftIO $
                    (DeviceArray len <$>) $
                      withForeignPtr fp $ \ !p -> do
                        !p' <- callocArray ccap
                        !fp' <- newForeignPtr finalizerFree p'
                        let fillRng :: Int -> Int -> IO (ForeignPtr a)
                            fillRng !n !i =
                              if i >= len
                                then return fp'
                                else do
                                  peekElemOff p n >>= pokeElemOff p' i
                                  fillRng (n + step) (i + 1)
                        fillRng start 0
                  !csvNew <- newTMVarEIO cs'
                  !clvNew <- newTVarEIO len
                  return
                    (ExtractAlone, someColumn $ InMemDevCol csvNew clvNew)

  derive'new'column (DbColumn !dba !dbc'offs) !sizer !deriver =
    readTMVarEIO (db'array'store dba) >>= \case
      Left !err -> throwHostEIO err
      Right (_shape, !hdr, DeviceArray !cap (fp0 :: ForeignPtr a)) -> do
        let !cs =
              DeviceArray
                (cap - dbc'offs)
                (plusForeignPtr fp0 $ dbc'offs * sizeOf (undefined :: a))
        !cl <-
          liftIO $
            subtract dbc'offs . fromIntegral <$> readDbArrayLength hdr

        let !cap' = sizer (cs, cl, deviceArrayCapacity cs)
        (_, !cs') <- liftIO $ newDeviceArray cap'
        !cl' <- deriver (cs, cl) (cs', cap')
        !csv' <- newTMVarEIO cs'
        !clv' <- newTVarEIO cl'
        return $ someColumn $ InMemDevCol csv' clv'

  extract'column'bool (DbColumn !dba !dbc'offs) !idxCol =
    readTMVarEIO (db'array'store dba) >>= \case
      Left !err -> throwHostEIO err
      Right (_shape, !hdr, DeviceArray _cap (fp0 :: ForeignPtr a)) -> do
        (!idxa, !idxl) <- view'column'data idxCol
        let !fp = plusForeignPtr fp0 $ dbc'offs * sizeOf (undefined :: a)
        !cl <-
          liftIO $ subtract dbc'offs . fromIntegral <$> readDbArrayLength hdr
        if idxl /= cl
          then
            throwEdhM
              UsageError
              $ T.pack $
                "bool index shape mismatch - " <> show idxl <> " vs "
                  <> show cl
          else do
            (!fp', !cl') <- liftIO $
              withForeignPtr fp $ \ !p -> do
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
                              liftIO $ peekElemOff p i >>= pokeElemOff p' n
                              extractAt (i + 1) (n + 1)
                extractAt 0 0
            let !cs' = DeviceArray cl fp'
            !csvNew <- newTMVarEIO cs'
            !clvNew <- newTVarEIO cl'
            return $ someColumn $ InMemDevCol csvNew clvNew

  extract'column'fancy (DbColumn !dba !dbc'offs) !idxCol =
    readTMVarEIO (db'array'store dba) >>= \case
      Left !err -> throwHostEIO err
      Right (_shape, _hdr, DeviceArray _cap (fp0 :: ForeignPtr a)) -> do
        (!idxa, !idxl) <- view'column'data idxCol
        let !fp = plusForeignPtr fp0 $ dbc'offs * sizeOf (undefined :: a)
        -- !cl <- subtract dbc'offs . fromIntegral <$> readDbArrayLength hdr
        !fp' <- liftIO $
          withForeignPtr fp $ \ !p -> do
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
        !csvNew <- newTMVarEIO cs'
        !clvNew <- newTVarEIO idxl
        return $ someColumn $ InMemDevCol csvNew clvNew
