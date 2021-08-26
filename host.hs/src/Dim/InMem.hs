module Dim.InMem where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import Data.Dynamic
import qualified Data.Vector.Mutable as MV
import Dim.Column
import Dim.DataType
import Dim.XCHG
import Foreign hiding (void)
import Language.Edh.EHI
import Type.Reflection
import Prelude

data InMemDevCol a = (Eq a, Storable a, EdhXchg a, Typeable a) =>
  InMemDevCol
  { im'devcol'storage :: !(TMVar (DeviceArray a)),
    im'devcol'length :: !(TVar Int)
  }

instance
  (Eq a, Storable a, EdhXchg a, Typeable a) =>
  ManagedColumn InMemDevCol DeviceArray a
  where
  view'column'data (InMemDevCol csv clv) exit = (exit =<<) $
    atomically $ do
      !cs <- readTMVar csv
      !cl <- readTVar clv
      return (cs, cl)

  read'column'length (InMemDevCol _csv clv) = readTVarIO clv

  grow'column'capacity (InMemDevCol csv clv) !newCap !exit = (exit =<<) $
    bracketOnError
      ( atomically $ do
          !cs <- takeTMVar csv
          !cl <- readTVar clv
          return (cs, cl)
      )
      (\(!cs, _cl) -> atomically $ void $ tryPutTMVar csv cs)
      $ \(!cs, !cl) -> do
        !cs' <- dupDeviceArray cs cl newCap
        atomically $ putTMVar csv cs'
        return (cs', cl)

  mark'column'length (InMemDevCol csv clv) !newLen = atomically $ do
    !cs <- readTMVar csv
    let !cap = deviceArrayCapacity cs
    if newLen < 0 || newLen > cap
      then
        error $
          "column length out of range: " <> show newLen <> " vs " <> show cap
      else writeTVar clv newLen

  view'column'slice (InMemDevCol csv clv) !start !stop !exit = (exit =<<) $
    atomically $ do
      !cs <- readTMVar csv
      let !cap = deviceArrayCapacity cs
      !cl <- readTVar clv
      if stop < start || start < 0 || stop > cap
        then
          error $
            "column slice range out of range: "
              <> show start
              <> ":"
              <> show stop
              <> " vs "
              <> show cap
        else do
          let !cs' = unsafeSliceDeviceArray cs start (cap - start)
              !len = max 0 $ min cl stop - start
          !csvNew <- newTMVar cs'
          !clvNew <- newTVar len
          return (StayComposed, someColumn $ InMemDevCol csvNew clvNew)

  copy'column'slice (InMemDevCol csv clv) !ccap !start !stop !step !exit =
    (exit =<<) $ do
      DeviceArray _cap (fp :: ForeignPtr a) <- atomically $ readTMVar csv
      !cl <- readTVarIO clv

      if stop < start || start < 0 || stop > cl
        then
          error $
            "column slice range out of range: "
              <> show start
              <> ":"
              <> show stop
              <> " vs "
              <> show cl
        else do
          let (q, r) = quotRem (stop - start) step
              !len = if r == 0 then abs q else 1 + abs q
          if ccap < len
            then
              error $
                "capacity too small: " <> show ccap <> " vs "
                  <> show start
                  <> ":"
                  <> show stop
                  <> ":"
                  <> show step
            else do
              !fp' <- withForeignPtr fp $ \ !p -> do
                !p' <- callocArray ccap
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
              atomically $ do
                !csvNew <- newTMVar cs'
                !clvNew <- newTVar len
                return (StayComposed, someColumn $ InMemDevCol csvNew clvNew)

  derive'new'column (InMemDevCol csv clv) !sizer (!deriver, !exit) = do
    (!cs, !cl) <- atomically $ do
      !cs <- readTMVar csv
      !cl <- readTVar clv
      return (cs, cl)
    let !cap' = sizer (cs, cl, deviceArrayCapacity cs)
    (_, !cs') <- newDeviceArray cap'
    !cl' <- deriver (cs, cl) (cs', cap')
    !csv' <- newTMVarIO cs'
    !clv' <- newTVarIO cl'
    exit $ InMemDevCol csv' clv'

  extract'column'bool (InMemDevCol csv clv) !idxCol !exit = do
    DeviceArray _cap (fp :: ForeignPtr a) <- atomically $ readTMVar csv
    !cl <- readTVarIO clv
    view'column'data idxCol $ \(!idxa, !idxl) ->
      if idxl /= cl
        then
          error $
            "bool index shape mismatch - " <> show idxl <> " vs " <> show cl
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
          (exit =<<) $
            atomically $ do
              !csvNew <- newTMVar cs'
              !clvNew <- newTVar cl'
              return $ someColumn $ InMemDevCol csvNew clvNew

  extract'column'fancy (InMemDevCol csv _clv) !idxCol !exit = do
    DeviceArray _cap (fp :: ForeignPtr a) <- atomically $ readTMVar csv
    -- !cl <- readTVarIO clv
    view'column'data idxCol $ \(!idxa, !idxl) -> do
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
      (exit =<<) $
        atomically $ do
          !csvNew <- newTMVar cs'
          !clvNew <- newTVar idxl
          return $ someColumn $ InMemDevCol csvNew clvNew

data InMemDirCol a = (Eq a, EdhXchg a, Typeable a) =>
  InMemDirCol
  { im'devdir'storage :: !(TMVar (DirectArray a)),
    im'devdir'length :: !(TVar Int)
  }

instance
  (Eq a, EdhXchg a, Typeable a) =>
  ManagedColumn InMemDirCol DirectArray a
  where
  view'column'data (InMemDirCol csv clv) exit = (exit =<<) $
    atomically $ do
      !cs <- readTMVar csv
      !cl <- readTVar clv
      return (cs, cl)

  read'column'length (InMemDirCol _csv clv) = readTVarIO clv

  grow'column'capacity (InMemDirCol csv clv) !newCap exit = (exit =<<) $
    bracketOnError
      ( atomically $ do
          !cs <- takeTMVar csv
          !cl <- readTVar clv
          return (cs, cl)
      )
      (\(!cs, _cl) -> atomically $ void $ tryPutTMVar csv cs)
      $ \(!cs, !cl) -> do
        !cs' <- dupDirectArray cs cl newCap
        atomically $ do
          putTMVar csv cs'
          return (cs', cl)

  mark'column'length (InMemDirCol csv clv) !newLen = atomically $ do
    !cs <- readTMVar csv
    let !cap = directArrayCapacity cs
    if newLen < 0 || newLen > cap
      then
        error $
          "column length out of range: " <> show newLen <> " vs " <> show cap
      else do
        writeTVar clv newLen
        return ()

  view'column'slice (InMemDirCol csv clv) !start !stop exit = (exit =<<) $
    atomically $ do
      !cs <- readTMVar csv
      let !cap = directArrayCapacity cs
      !cl <- readTVar clv
      if stop < start || start < 0 || stop > cap
        then
          error $
            "column slice range out of range: "
              <> show start
              <> ":"
              <> show stop
              <> " vs "
              <> show cap
        else do
          let !cs' = unsafeSliceDirectArray cs start (cap - start)
              !len = max 0 $ min cl stop - start
          !csvNew <- newTMVar cs'
          !clvNew <- newTVar len
          return (StayComposed, someColumn $ InMemDirCol csvNew clvNew)

  copy'column'slice (InMemDirCol csv clv) !ccap !start !stop !step exit =
    (exit =<<) $ do
      DirectArray !iov <- atomically $ readTMVar csv
      !cl <- readTVarIO clv

      if stop < start || start < 0 || stop > cl
        then
          error $
            "column slice range out of range: "
              <> show start
              <> ":"
              <> show stop
              <> " vs "
              <> show cl
        else do
          let (q, r) = quotRem (stop - start) step
              !len = if r == 0 then abs q else 1 + abs q
          if ccap < len
            then
              error $
                "capacity too small: " <> show ccap <> " vs "
                  <> show start
                  <> ":"
                  <> show stop
                  <> ":"
                  <> show step
            else do
              !iov' <- do
                !iov' <- MV.unsafeNew ccap
                let fillRng :: Int -> Int -> IO ()
                    fillRng !n !i =
                      if i >= len
                        then return ()
                        else do
                          MV.unsafeRead iov n >>= MV.unsafeWrite iov' i
                          fillRng (n + step) (i + 1)
                fillRng start 0
                return iov'
              let !cs' = DirectArray iov'
              atomically $ do
                !csvNew <- newTMVar cs'
                !clvNew <- newTVar len
                return
                  (StayComposed, someColumn $ InMemDirCol csvNew clvNew)

  derive'new'column (InMemDirCol csv clv) !sizer (!deriver, !exit) = do
    (!cs, !cl) <- atomically $ do
      !cs <- readTMVar csv
      !cl <- readTVar clv
      return (cs, cl)
    let !cap' = sizer (cs, cl, directArrayCapacity cs)
    (_, !cs') <- newDirectArray @a cap'
    !cl' <- deriver (cs, cl) (cs', cap')
    !csv' <- newTMVarIO cs'
    !clv' <- newTVarIO cl'
    exit $ InMemDirCol csv' clv'

  extract'column'bool (InMemDirCol csv clv) !idxCol exit = do
    DirectArray !iov <- atomically $ readTMVar csv
    !cl <- readTVarIO clv
    view'column'data idxCol $ \(!idxa, !idxl) ->
      if idxl /= cl
        then
          error $
            "bool index shape mismatch - " <> show idxl <> " vs " <> show cl
        else do
          (!iov', !cl') <- do
            !iov' <- MV.new cl
            let extractAt :: Int -> Int -> IO (MV.IOVector a, Int)
                extractAt !i !n =
                  if i >= cl
                    then return (iov', n)
                    else do
                      array'reader idxa i >>= \case
                        YesNo 0 -> extractAt (i + 1) n
                        _ -> do
                          MV.unsafeRead iov i >>= MV.unsafeWrite iov' n
                          extractAt (i + 1) (n + 1)
            extractAt 0 0
          let !cs' = DirectArray iov'
          (exit =<<) $
            atomically $ do
              !csvNew <- newTMVar cs'
              !clvNew <- newTVar cl'
              return $ someColumn $ InMemDirCol csvNew clvNew

  extract'column'fancy (InMemDirCol csv _clv) !idxCol exit = do
    DirectArray !iov <- atomically $ readTMVar csv
    -- !cl <- readTVar clv
    view'column'data idxCol $ \(!idxa, !idxl) -> do
      !iov' <- do
        !iov' <- MV.new idxl
        let extractAt :: Int -> IO (MV.IOVector a)
            extractAt !i =
              if i >= idxl
                then return iov'
                else do
                  !idxi <- array'reader idxa i
                  MV.unsafeRead iov idxi >>= MV.unsafeWrite iov' i
                  extractAt (i + 1)
        extractAt 0
      let !cs' = DirectArray iov'
      (exit =<<) $
        atomically $ do
          !csvNew <- newTMVar cs'
          !clvNew <- newTVar idxl
          return $ someColumn $ InMemDirCol csvNew clvNew

createInMemColumn ::
  forall a.
  DataType a ->
  ArrayCapacity ->
  ArrayLength ->
  EdhTxExit SomeColumn ->
  EdhTx
createInMemColumn !gdt !cap !len !exit !ets = runEdhTx ets $ case gdt of
  DeviceDt dt -> device'data'type'holder dt $ \(_ :: TypeRep a) ->
    edhContIO $
      newDeviceArray @a cap >>= \(_fp, !cs) -> atomically $ do
        !csv <- newTMVar cs
        !clv <- newTVar len
        exitEdh ets exit $ someColumn $ InMemDevCol csv clv
  DirectDt dt -> direct'data'defv'holder dt $ \(defv :: a) ->
    edhContIO $
      newDirectArray' defv cap >>= \(_iov, !cs) -> atomically $ do
        !csv <- newTMVar cs
        !clv <- newTVar len
        exitEdh ets exit $ someColumn $ InMemDirCol csv clv
