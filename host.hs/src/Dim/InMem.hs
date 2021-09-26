module Dim.InMem where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import Control.Monad.IO.Class
import Data.Dynamic
import qualified Data.Text as T
import qualified Data.Vector.Mutable as MV
import Dim.Column
import Dim.DataType
import Dim.FlatArray
import Dim.XCHG
import Foreign hiding (void)
import Language.Edh.MHI
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
  view'column'data (InMemDevCol csv clv) = atomicallyEIO $ do
    !cs <- readTMVar csv
    !cl <- readTVar clv
    return (cs, cl)

  read'column'length (InMemDevCol _csv clv) = readTVarEIO clv

  grow'column'capacity (InMemDevCol csv clv) !newCap = liftIO $
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

  mark'column'length (InMemDevCol csv clv) !newLen = do
    !cs <- readTMVarEIO csv
    let !cap = deviceArrayCapacity cs
    if newLen < 0 || newLen > cap
      then
        throwEIO UsageError $
          T.pack $
            "column length out of range: " <> show newLen <> " vs " <> show cap
      else writeTVarEIO clv newLen

  view'column'slice (InMemDevCol csv clv) !start !stop = do
    !cs <- readTMVarEIO csv
    let !cap = deviceArrayCapacity cs
    !cl <- readTVarEIO clv
    if stop < start || start < 0 || stop > cap
      then
        throwEIO UsageError $
          T.pack $
            "column slice range out of range: "
              <> show start
              <> ":"
              <> show stop
              <> " vs "
              <> show cap
      else do
        let !cs' = unsafeSliceDeviceArray cs start (cap - start)
            !len = max 0 $ min cl stop - start
        !csvNew <- newTMVarEIO cs'
        !clvNew <- newTVarEIO len
        return (StayComposed, someColumn $ InMemDevCol csvNew clvNew)

  copy'column'slice (InMemDevCol csv clv) !ccap !start !stop !step = do
    DeviceArray _cap (fp :: ForeignPtr a) <- readTMVarEIO csv
    !cl <- readTVarEIO clv
    if stop < start || start < 0 || stop > cl
      then
        throwEIO UsageError $
          T.pack $
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
            throwEIO UsageError $
              T.pack $
                "capacity too small: " <> show ccap <> " vs "
                  <> show start
                  <> ":"
                  <> show stop
                  <> ":"
                  <> show step
          else do
            !fp' <- liftIO $
              withForeignPtr fp $ \ !p -> do
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
            !csvNew <- newTMVarEIO cs'
            !clvNew <- newTVarEIO len
            return (StayComposed, someColumn $ InMemDevCol csvNew clvNew)

  derive'new'column (InMemDevCol csv clv) !sizer !deriver = do
    (!cs, !cl) <- atomicallyEIO $ do
      !cs <- readTMVar csv
      !cl <- readTVar clv
      return (cs, cl)
    let !cap' = sizer (cs, cl, deviceArrayCapacity cs)
    (_, !cs') <- liftIO $ newDeviceArray cap'
    !cl' <- deriver (cs, cl) (cs', cap')
    !csv' <- newTMVarEIO cs'
    !clv' <- newTVarEIO cl'
    return $ someColumn $ InMemDevCol csv' clv'

  extract'column'bool (InMemDevCol csv clv) !idxCol = do
    DeviceArray _cap (fp :: ForeignPtr a) <- readTMVarEIO csv
    !cl <- readTVarEIO clv
    (!idxa, !idxl) <- view'column'data idxCol
    if idxl /= cl
      then
        throwEIO UsageError $
          T.pack $
            "bool index shape mismatch - " <> show idxl <> " vs " <> show cl
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
                          peekElemOff p i >>= pokeElemOff p' n
                          extractAt (i + 1) (n + 1)
            extractAt 0 0
        let !cs' = DeviceArray cl fp'
        !csvNew <- newTMVarEIO cs'
        !clvNew <- newTVarEIO cl'
        return $ someColumn $ InMemDevCol csvNew clvNew

  extract'column'fancy (InMemDevCol csv _clv) !idxCol = do
    DeviceArray _cap (fp :: ForeignPtr a) <- readTMVarEIO csv
    -- !cl <- readTVarIO clv
    (!idxa, !idxl) <- view'column'data idxCol
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

data InMemDirCol a = (Eq a, EdhXchg a, Typeable a) =>
  InMemDirCol
  { im'devdir'storage :: !(TMVar (DirectArray a)),
    im'devdir'length :: !(TVar Int)
  }

instance
  (Eq a, EdhXchg a, Typeable a) =>
  ManagedColumn InMemDirCol DirectArray a
  where
  view'column'data (InMemDirCol csv clv) = do
    !cs <- readTMVarEIO csv
    !cl <- readTVarEIO clv
    return (cs, cl)

  read'column'length (InMemDirCol _csv clv) = readTVarEIO clv

  grow'column'capacity (InMemDirCol csv clv) !newCap = liftIO $
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

  mark'column'length (InMemDirCol csv clv) !newLen = do
    !cs <- readTMVarEIO csv
    let !cap = directArrayCapacity cs
    if newLen < 0 || newLen > cap
      then
        throwEIO UsageError $
          T.pack $
            "column length out of range: " <> show newLen <> " vs " <> show cap
      else writeTVarEIO clv newLen

  view'column'slice (InMemDirCol csv clv) !start !stop = do
    !cs <- readTMVarEIO csv
    let !cap = directArrayCapacity cs
    !cl <- readTVarEIO clv
    if stop < start || start < 0 || stop > cap
      then
        throwEIO UsageError $
          T.pack $
            "column slice range out of range: "
              <> show start
              <> ":"
              <> show stop
              <> " vs "
              <> show cap
      else do
        let !cs' = unsafeSliceDirectArray cs start (cap - start)
            !len = max 0 $ min cl stop - start
        !csvNew <- newTMVarEIO cs'
        !clvNew <- newTVarEIO len
        return (StayComposed, someColumn $ InMemDirCol csvNew clvNew)

  copy'column'slice (InMemDirCol csv clv) !ccap !start !stop !step = do
    DirectArray !iov <- readTMVarEIO csv
    !cl <- readTVarEIO clv

    if stop < start || start < 0 || stop > cl
      then
        throwEIO UsageError $
          T.pack $
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
            throwEIO UsageError $
              T.pack $
                "capacity too small: " <> show ccap <> " vs "
                  <> show start
                  <> ":"
                  <> show stop
                  <> ":"
                  <> show step
          else do
            !iov' <- liftIO $ do
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
            !csvNew <- newTMVarEIO cs'
            !clvNew <- newTVarEIO len
            return
              (StayComposed, someColumn $ InMemDirCol csvNew clvNew)

  derive'new'column (InMemDirCol csv clv) !sizer !deriver = do
    (!cs, !cl) <- atomicallyEIO $ do
      !cs <- readTMVar csv
      !cl <- readTVar clv
      return (cs, cl)
    let !cap' = sizer (cs, cl, directArrayCapacity cs)
    (_, !cs') <- liftIO $ newDirectArray @a cap'
    !cl' <- deriver (cs, cl) (cs', cap')
    !csv' <- newTMVarEIO cs'
    !clv' <- newTVarEIO cl'
    return $ someColumn $ InMemDirCol csv' clv'

  extract'column'bool (InMemDirCol csv clv) !idxCol = do
    DirectArray !iov <- readTMVarEIO csv
    !cl <- readTVarEIO clv
    (!idxa, !idxl) <- view'column'data idxCol
    if idxl /= cl
      then
        throwEIO UsageError $
          T.pack $
            "bool index shape mismatch - " <> show idxl <> " vs " <> show cl
      else do
        (!iov', !cl') <- liftIO $ do
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
        !csvNew <- newTMVarEIO cs'
        !clvNew <- newTVarEIO cl'
        return $ someColumn $ InMemDirCol csvNew clvNew

  extract'column'fancy (InMemDirCol csv _clv) !idxCol = do
    DirectArray !iov <- readTMVarEIO csv
    -- !cl <- readTVar clv
    (!idxa, !idxl) <- view'column'data idxCol
    !iov' <- liftIO $ do
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
    !csvNew <- newTMVarEIO cs'
    !clvNew <- newTVarEIO idxl
    return $ someColumn $ InMemDirCol csvNew clvNew

createInMemColumn ::
  forall a.
  DataType a ->
  ArrayCapacity ->
  ArrayLength ->
  Edh SomeColumn
createInMemColumn !gdt !cap !len =
  createInMemColumn' gdt cap len $ return . someColumn

createInMemColumn' ::
  forall a r.
  DataType a ->
  ArrayCapacity ->
  ArrayLength ->
  ( forall c f.
    ( ManagedColumn c f a,
      Typeable (c a),
      Typeable (f a),
      Typeable c,
      Typeable f
    ) =>
    c a ->
    Edh r
  ) ->
  Edh r
createInMemColumn' !gdt !cap !len exit = case gdt of
  DeviceDt dt -> case device'data'type dt of
    (_ :: TypeRep a) -> do
      (_fp, !cs) <- liftIO $ newDeviceArray @a cap
      !csv <- newTMVarEdh cs
      !clv <- newTVarEdh len
      exit $ InMemDevCol csv clv
  DirectDt dt -> do
    let defv = direct'data'default dt
    (_iov, !cs) <- liftIO $ newDirectArray' defv cap
    !csv <- newTMVarEdh cs
    !clv <- newTVarEdh len
    exit $ InMemDirCol csv clv
  DummyDt dti -> naM $ "you don't create Column from a dummy dtype: " <> dti
