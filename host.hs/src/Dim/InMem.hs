{-# LANGUAGE MultiParamTypeClasses #-}

module Dim.InMem where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import Data.Dynamic
import qualified Data.Text as T
import qualified Data.Vector.Mutable as MV
import Dim.Column
import Dim.DataType
import Dim.XCHG
import Foreign hiding (void)
import Language.Edh.EHI
import Prelude

data InMemDevCol a = (EdhXchg a, Storable a, Typeable a) =>
  InMemDevCol
  { im'devcol'storage :: !(TMVar (DeviceArray a)),
    im'devcol'length :: !(TVar Int)
  }

instance
  (EdhXchg a, Storable a, Typeable a) =>
  ManagedColumn InMemDevCol DeviceArray a
  where
  view'column'data (InMemDevCol csv clv) !exit !ets = do
    !cs <- readTMVar csv
    !cl <- readTVar clv
    exitEdh ets exit (cs, cl)

  read'column'length (InMemDevCol _csv clv) !exit !ets =
    exitEdh ets exit =<< readTVar clv

  grow'column'capacity (InMemDevCol csv clv) !newCap !exit !ets =
    runEdhTx ets $
      edhContIO $
        bracketOnError
          ( atomically $ do
              !cs <- takeTMVar csv
              !cl <- readTVar clv
              return (cs, cl)
          )
          (\(!cs, _cl) -> atomically $ void $ tryPutTMVar csv cs)
          $ \(!cs, !cl) -> do
            cs' <- dupDeviceArray cs cl newCap
            atomically $ do
              putTMVar csv cs'
              exitEdh ets exit (cs', cl)

  mark'column'length (InMemDevCol csv clv) !newLen !exit !ets = do
    !cs <- readTMVar csv
    let !cap = deviceArrayCapacity cs
    if newLen < 0 || newLen > cap
      then
        throwEdh ets UsageError $
          "column length out of range: "
            <> T.pack (show newLen)
            <> " vs "
            <> T.pack (show cap)
      else do
        writeTVar clv newLen
        exitEdh ets exit ()

  view'column'slice (InMemDevCol csv clv) !start !stop !exit !ets = do
    !cs <- readTMVar csv
    let !cap = deviceArrayCapacity cs
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
        let !cs' = unsafeSliceDeviceArray cs start (cap - start)
            !len = max 0 $ min cl stop - start
        !csvNew <- newTMVar cs'
        !clvNew <- newTVar len
        exitEdh ets exit (StayComposed, InMemDevCol csvNew clvNew)

  copy'column'slice (InMemDevCol csv clv) !start !stop !step !exit !ets =
    do
      DeviceArray !cap (fp :: ForeignPtr a) <- readTMVar csv
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
        else
          runEdhTx ets $
            edhContIO $
              if start >= cap || stop == start
                then do
                  !csNew <- emptyDeviceArray @a
                  atomically $ do
                    !csvNew <- newTMVar csNew
                    !clvNew <- newTVar 0
                    exitEdh
                      ets
                      exit
                      (StayComposed, InMemDevCol csvNew clvNew)
                else do
                  let (q, r) = quotRem (stop - start) step
                      !len = if r == 0 then abs q else 1 + abs q
                  !fp' <- withForeignPtr fp $ \ !p -> do
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
                  atomically $ do
                    !csvNew <- newTMVar cs'
                    !clvNew <- newTVar len
                    exitEdh
                      ets
                      exit
                      (StayComposed, InMemDevCol csvNew clvNew)

data InMemDirCol a = (EdhXchg a, Eq a, Typeable a) =>
  InMemDirCol
  { im'devdir'storage :: !(TMVar (DirectArray a)),
    im'devdir'length :: !(TVar Int)
  }

instance
  (EdhXchg a, Eq a, Typeable a) =>
  ManagedColumn InMemDirCol DirectArray a
  where
  view'column'data (InMemDirCol csv clv) !exit !ets = do
    !cs <- readTMVar csv
    !cl <- readTVar clv
    exitEdh ets exit (cs, cl)

  read'column'length (InMemDirCol _csv clv) !exit !ets =
    exitEdh ets exit =<< readTVar clv

  grow'column'capacity (InMemDirCol csv clv) !newCap !exit !ets =
    runEdhTx ets $
      edhContIO $
        bracketOnError
          ( atomically $ do
              !cs <- takeTMVar csv
              !cl <- readTVar clv
              return (cs, cl)
          )
          (\(!cs, _cl) -> atomically $ void $ tryPutTMVar csv cs)
          $ \(!cs, !cl) -> do
            cs' <- dupDirectArray cs cl newCap
            atomically $ do
              putTMVar csv cs'
              exitEdh ets exit (cs', cl)

  mark'column'length (InMemDirCol csv clv) !newLen !exit !ets = do
    !cs <- readTMVar csv
    let !cap = directArrayCapacity cs
    if newLen < 0 || newLen > cap
      then
        throwEdh ets UsageError $
          "column length out of range: "
            <> T.pack (show newLen)
            <> " vs "
            <> T.pack (show cap)
      else do
        writeTVar clv newLen
        exitEdh ets exit ()

  view'column'slice (InMemDirCol csv clv) !start !stop !exit !ets = do
    !cs <- readTMVar csv
    let !cap = directArrayCapacity cs
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
        let !cs' = unsafeSliceDirectArray cs start (cap - start)
            !len = max 0 $ min cl stop - start
        !csvNew <- newTMVar cs'
        !clvNew <- newTVar len
        exitEdh ets exit (StayComposed, InMemDirCol csvNew clvNew)

  copy'column'slice (InMemDirCol csv clv) !start !stop !step !exit !ets =
    do
      DirectArray !iov <- readTMVar csv
      !cl <- readTVar clv
      let cap = MV.length iov

      if stop < start || start < 0 || stop > cl
        then
          throwEdh ets UsageError $
            "column slice range out of range: "
              <> T.pack (show start)
              <> ":"
              <> T.pack (show stop)
              <> " vs "
              <> T.pack (show cl)
        else
          runEdhTx ets $
            edhContIO $
              if start >= cap || stop == start
                then do
                  !csNew <- emptyDirectArray @a
                  atomically $ do
                    !csvNew <- newTMVar csNew
                    !clvNew <- newTVar 0
                    exitEdh
                      ets
                      exit
                      (StayComposed, InMemDirCol csvNew clvNew)
                else do
                  let (q, r) = quotRem (stop - start) step
                      !len = if r == 0 then abs q else 1 + abs q
                  !iov' <- do
                    !iov' <- MV.unsafeNew len
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
                    exitEdh
                      ets
                      exit
                      (StayComposed, InMemDirCol csvNew clvNew)
