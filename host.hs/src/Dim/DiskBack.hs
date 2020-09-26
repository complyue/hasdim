
module Dim.DiskBack where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Foreign                 hiding ( void )

import           Control.Exception
import           Control.Concurrent.STM

import qualified Data.Text                     as T

import qualified Data.Vector.Mutable           as MV

import           Data.List.NonEmpty             ( NonEmpty(..) )

import           Language.Edh.EHI

import           Dim.DataType
import           Dim.Column
import           Dim.DbArray
import           Dim.InMem


data DbColumn = DbColumn {
    db'column'array :: !DbArray
  , db'column'offset :: !Int
  }

instance ManagedColumn DbColumn where
  data'type'of'column = db'array'dtype . db'column'array

  view'column'data (DbColumn !dba !dbc'offs) =
    readTMVar (db'array'store dba) >>= \case
      Left !err -> throwSTM err
      Right (_shape, _hdr, !dbcs) ->
        return
          $ unsafeSliceFlatArray dbcs dbc'offs
          $ flatArrayCapacity dbcs
          - dbc'offs

  read'column'length (DbColumn !dba !dbc'offs) =
    readTMVar (db'array'store dba) >>= \case
      Left  !err                  -> throwSTM err
      Right (_shape, !hdr, _dbcs) -> do
        !dba'len <- fromIntegral <$> unsafeIOToSTM (readDbArrayLength hdr)
        return $ dba'len - dbc'offs

  grow'column'capacity (DbColumn !dba !dbc'offs) !newCap !exit !ets =
    if edh'in'tx ets
      then throwEdh ets
                    UsageError
                    "you don't grow a disk backed column from within a tx"
      else
        runEdhTx ets
        $ edhContIO
        $ bracket (atomically $ takeTMVar dbas) (atomically . tryPutTMVar dbas)
        $ const
        $ do
            mmapDbArray dbas
                        (db'array'dir dba)
                        (db'array'path dba)
                        (db'array'dtype dba)
                        (Just $ ArrayShape $ ("", newCap + dbc'offs) :| [])
            atomically
              $   runEdhTx ets
              $   edhContSTM
              $   readTMVar (db'array'store dba)
              >>= \case
                    Left !err -> throwSTM err
                    Right (_shape, _hdr, !dbcs) ->
                      exit
                        $ unsafeSliceFlatArray dbcs dbc'offs
                        $ flatArrayCapacity dbcs
                        - dbc'offs
    where !dbas = db'array'store dba

  mark'column'length (DbColumn !dba !dbc'offs) !newLen !exit !ets =
    readTMVar (db'array'store dba) >>= \case
      Left  !err                  -> throwSTM err
      Right (_shape, !hdr, !dbcs) -> do
        let !cap = flatArrayCapacity dbcs
        if newLen' < 0 || newLen' > cap
          then
            throwEdh ets UsageError
            $  "column length out of range: "
            <> T.pack (show newLen)
            <> " vs "
            <> T.pack (show $ cap - dbc'offs)
          else do
            unsafeIOToSTM (writeDbArrayLength hdr $ fromIntegral newLen')
            exit
    where !newLen' = newLen + dbc'offs

  view'column'slice (DbColumn !dba !dbc'offs) !start !stop !exit !ets =
    readTMVar (db'array'store dba) >>= \case
      Left  !err                  -> throwSTM err
      Right (_shape, !hdr, _dbcs) -> do
        !dba'len <- fromIntegral <$> unsafeIOToSTM (readDbArrayLength hdr)
        if dbc'offs + stop == dba'len
          then exit True $ Column $ DbColumn dba $ dbc'offs + start
          else throwEdh
            ets
            UsageError
            "can only view slice of a disk backed column to its full length"

  copy'column'slice (DbColumn !dba !dbc'offs) !start !stop !step !exit !ets =
    readTMVar (db'array'store dba) >>= \case
      Left  !err                  -> throwSTM err
      Right (_shape, !hdr, !dbcs) -> do
        !dba'len <- fromIntegral <$> unsafeIOToSTM (readDbArrayLength hdr)
        let
          !dt = db'array'dtype dba
          !cs =
            unsafeSliceFlatArray dbcs dbc'offs
              $ flatArrayCapacity dbcs
              - dbc'offs
          !cl = dba'len - dbc'offs

        if stop < start || start < 0 || stop > cl
          then
            throwEdh ets UsageError
            $  "column slice range out of range: "
            <> T.pack (show start)
            <> ":"
            <> T.pack (show stop)
            <> " vs "
            <> T.pack (show cl)
          else case cs of
            DeviceArray !cap (fp :: ForeignPtr a) ->
              if start >= cap || stop == start
                then do
                  !csvNew <- newTVar (emptyDeviceArray @a)
                  !clvNew <- newTVar 0
                  exit False $ Column $ InMemColumn dt csvNew clvNew
                else do
                  let (q, r) = quotRem (stop - start) step
                      !len   = if r == 0 then abs q else 1 + abs q
                  !fp' <- unsafeIOToSTM $ withForeignPtr fp $ \ !p -> do
                    !p'  <- callocArray len
                    !fp' <- newForeignPtr finalizerFree p'
                    let fillRng :: Int -> Int -> IO ()
                        fillRng !n !i = if i >= len
                          then return ()
                          else do
                            peekElemOff p n >>= pokeElemOff p' i
                            fillRng (n + step) (i + 1)
                    fillRng start 0
                    return fp'
                  let !cs' = DeviceArray len fp'
                  !csvNew <- newTVar cs'
                  !clvNew <- newTVar len
                  exit False $ Column $ InMemColumn dt csvNew clvNew
            HostArray !cap (ha :: MV.IOVector a) ->
              if start >= cap || stop == start
                then do
                  !csvNew <- newTVar (emptyHostArray @a)
                  !clvNew <- newTVar 0
                  exit False $ Column $ InMemColumn dt csvNew clvNew
                else do
                  let (q, r) = quotRem (stop - start) step
                      !len   = if r == 0 then abs q else 1 + abs q
                  !ha' <- unsafeIOToSTM $ do
                    !ha' <- MV.unsafeNew len
                    let fillRng :: Int -> Int -> IO ()
                        fillRng !n !i = if i >= len
                          then return ()
                          else do
                            MV.unsafeRead ha n >>= MV.unsafeWrite ha' i
                            fillRng (n + step) (i + 1)
                    fillRng start 0
                    return ha'
                  let !cs' = HostArray len ha'
                  !csvNew <- newTVar cs'
                  !clvNew <- newTVar len
                  exit False $ Column $ InMemColumn dt csvNew clvNew

  extract'column'bool (DbColumn !dba !dbc'offs) (Column !colMask) !naExit !exit !ets
    = readTMVar (db'array'store dba) >>= \case
      Left  !err                  -> throwSTM err
      Right (_shape, !hdr, !dbcs) -> do
        !dba'len <- fromIntegral <$> unsafeIOToSTM (readDbArrayLength hdr)
        let
          !dt = db'array'dtype dba
          !cs =
            unsafeSliceFlatArray dbcs dbc'offs
              $ flatArrayCapacity dbcs
              - dbc'offs
          !cl = dba'len - dbc'offs

        resolveDataOperator' ets (data'type'identifier dt) cs naExit
          $ \ !dtOp -> do
              let !fa = unsafeSliceFlatArray cs 0 cl
              !mcl <- read'column'length colMask
              if mcl /= cl
                then
                  throwEdh ets UsageError
                  $  "index length mismatch: "
                  <> T.pack (show mcl)
                  <> " vs "
                  <> T.pack (show cl)
                else do
                  !mcs <- view'column'data colMask
                  let !ma = unsafeSliceFlatArray mcs 0 mcl
                  flat'extract'yesno dtOp ets ma fa $ \(!rfa, !rlen) -> do
                    !csvRtn <- newTVar rfa
                    !clvRtn <- newTVar rlen
                    exit False $ Column $ InMemColumn dt csvRtn clvRtn

  extract'column'fancy (DbColumn !dba !dbc'offs) (Column !colIdx) !naExit !exit !ets
    = readTMVar (db'array'store dba) >>= \case
      Left  !err                  -> throwSTM err
      Right (_shape, !hdr, !dbcs) -> do
        !dba'len <- fromIntegral <$> unsafeIOToSTM (readDbArrayLength hdr)
        let
          !dt = db'array'dtype dba
          !cs =
            unsafeSliceFlatArray dbcs dbc'offs
              $ flatArrayCapacity dbcs
              - dbc'offs
          !cl = dba'len - dbc'offs

        !icl <- read'column'length colIdx
        !ics <- view'column'data colIdx
        resolveDataOperator' ets (data'type'identifier dt) cs naExit
          $ \ !dtOp -> do
              let !ifa = unsafeSliceFlatArray ics 0 icl
                  !fa  = unsafeSliceFlatArray cs 0 cl
              flat'extract'fancy dtOp ets ifa fa $ \ !rfa -> do
                !csvRtn <- newTVar rfa
                !clvRtn <- newTVar icl
                exit False $ Column $ InMemColumn dt csvRtn clvRtn

