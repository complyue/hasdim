module Dim.InMem where

-- import           Debug.Trace

import Control.Concurrent.STM
  ( STM,
    TVar,
    newTVar,
    readTVar,
    writeTVar,
  )
import qualified Data.Text as T
import qualified Data.Vector.Mutable as MV
import Dim.Column
import Dim.DataType
import Foreign hiding (void)
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.EHI
import Prelude

data InMemColumn = InMemColumn
  { im'column'data'type :: !DataType,
    im'column'storage :: !(TVar FlatArray),
    im'column'length :: !(TVar Int)
  }

createInMemColumn :: DataType -> Int -> Int -> (Column -> STM ()) -> EdhTx
createInMemColumn !dt !cap !len !exit !ets =
  if cap < 0 || len < 0 || len > cap
    then
      throwEdh ets UsageError $
        "bad len/cap: "
          <> T.pack (show len)
          <> "/"
          <> T.pack (show cap)
    else do
      !cs <- flat'new'array dt cap
      !csv <- newTVar cs
      !clv <- newTVar len
      exit $ Column $ InMemColumn dt csv clv

instance ManagedColumn InMemColumn where
  data'type'of'column = im'column'data'type
  view'column'data = readTVar . im'column'storage
  read'column'length = readTVar . im'column'length

  grow'column'capacity (InMemColumn !dt !csv _clv) !newCap !exit _ets = do
    !cs <- readTVar csv
    !cs' <- flat'grow'array dt cs newCap
    writeTVar csv cs'
    exit cs'

  mark'column'length (InMemColumn _dt !csv !clv) !newLen !exit !ets = do
    !cs <- readTVar csv
    let !cap = flatArrayCapacity cs
    if newLen < 0 || newLen > cap
      then
        throwEdh ets UsageError $
          "column length out of range: "
            <> T.pack (show newLen)
            <> " vs "
            <> T.pack (show cap)
      else writeTVar clv newLen >> exit

  view'column'slice (InMemColumn !dt !csv !clv) !start !stop !exit !ets = do
    !cs <- readTVar csv
    let !cap = flatArrayCapacity cs
    !cl <- readTVar clv
    if stop < start || start < 0 || stop > cap
      then
        throwEdh ets UsageError $
          "column slice range out of range: "
            <> T.pack (show start)
            <> ":"
            <> T.pack (show stop)
            <> " vs "
            <> T.pack (show cap)
      else do
        let !cs' = unsafeSliceFlatArray cs start (cap - start)
            !len = max 0 $ min cl stop - start
        !csvNew <- newTVar cs'
        !clvNew <- newTVar len
        exit True $ Column $ InMemColumn dt csvNew clvNew

  copy'column'slice (InMemColumn !dt !csv !clv) !start !stop !step !exit !ets =
    do
      !cs <- readTVar csv
      !cl <- readTVar clv

      if stop < start || start < 0 || stop > cl
        then
          throwEdh ets UsageError $
            "column slice range out of range: "
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
                exit True $ Column $ InMemColumn dt csvNew clvNew
              else do
                let (q, r) = quotRem (stop - start) step
                    !len = if r == 0 then abs q else 1 + abs q
                !fp' <- unsafeIOToSTM $
                  withForeignPtr fp $ \ !p -> do
                    !p' <- callocArray len
                    !fp' <- newForeignPtr finalizerFree p'
                    let fillRng :: Int -> Int -> IO ()
                        fillRng !n !i =
                          if i >= len
                            then return ()
                            else do
                              peekElemOff p n >>= pokeElemOff p' i
                              fillRng (n + step) (i + 1)
                    fillRng start 0
                    return fp'
                let !cs' = DeviceArray len fp'
                !csvNew <- newTVar cs'
                !clvNew <- newTVar len
                exit True $ Column $ InMemColumn dt csvNew clvNew
          HostArray !cap (ha :: MV.IOVector a) ->
            if start >= cap || stop == start
              then do
                !csvNew <- newTVar (emptyHostArray @a)
                !clvNew <- newTVar 0
                exit True $ Column $ InMemColumn dt csvNew clvNew
              else do
                let (q, r) = quotRem (stop - start) step
                    !len = if r == 0 then abs q else 1 + abs q
                !ha' <- unsafeIOToSTM $ do
                  !ha' <- MV.unsafeNew len
                  let fillRng :: Int -> Int -> IO ()
                      fillRng !n !i =
                        if i >= len
                          then return ()
                          else do
                            MV.unsafeRead ha n >>= MV.unsafeWrite ha' i
                            fillRng (n + step) (i + 1)
                  fillRng start 0
                  return ha'
                let !cs' = HostArray len ha'
                !csvNew <- newTVar cs'
                !clvNew <- newTVar len
                exit True $ Column $ InMemColumn dt csvNew clvNew

  extract'column'bool (InMemColumn !dt !csv !clv) (Column !colMask) !naExit !exit !ets =
    do
      !cs <- readTVar csv
      !cl <- readTVar clv

      resolveDataOperator' ets (data'type'identifier dt) cs naExit $ \ !dtOp ->
        do
          let !fa = unsafeSliceFlatArray cs 0 cl
          !mcl <- read'column'length colMask
          if mcl /= cl
            then
              throwEdh ets UsageError $
                "index length mismatch: "
                  <> T.pack (show mcl)
                  <> " vs "
                  <> T.pack (show cl)
            else do
              !mcs <- view'column'data colMask
              let !ma = unsafeSliceFlatArray mcs 0 mcl
              flat'extract'yesno dtOp ets ma fa $ \(!rfa, !rlen) -> do
                !csvRtn <- newTVar rfa
                !clvRtn <- newTVar rlen
                exit True $ Column $ InMemColumn dt csvRtn clvRtn

  extract'column'fancy (InMemColumn !dt !csv !clv) (Column !colIdx) !naExit !exit !ets =
    do
      !cs <- readTVar csv
      !cl <- readTVar clv

      !icl <- read'column'length colIdx
      !ics <- view'column'data colIdx
      resolveDataOperator' ets (data'type'identifier dt) cs naExit $ \ !dtOp ->
        do
          let !ifa = unsafeSliceFlatArray ics 0 icl
              !fa = unsafeSliceFlatArray cs 0 cl
          flat'extract'fancy dtOp ets ifa fa $ \ !rfa -> do
            !csvRtn <- newTVar rfa
            !clvRtn <- newTVar icl
            exit True $ Column $ InMemColumn dt csvRtn clvRtn
