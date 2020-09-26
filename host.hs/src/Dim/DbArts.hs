{-# LANGUAGE AllowAmbiguousTypes #-}

module Dim.DbArts where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Foreign.ForeignPtr.Unsafe
import           Foreign                 hiding ( void )
import qualified Data.ByteString               as B
import qualified Data.ByteString.Internal      as B

import           System.FilePath
import           System.Directory
import           System.IO
import           System.IO.MMap

import           Control.Monad
import           Control.Exception
import           Control.Concurrent.STM

import           Data.List.NonEmpty             ( NonEmpty(..) )
import qualified Data.List.NonEmpty            as NE

import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.Proxy
import           Data.Dynamic

import qualified Data.Vector.Storable          as VS
import qualified Data.Vector.Storable.Mutable  as MVS


import qualified Data.Lossless.Decimal         as D
import           Language.Edh.EHI

import           Dim.XCHG
import           Dim.DataType
import           Dim.DbArray


createDbArrayClass :: Object -> Scope -> STM Object
createDbArrayClass !defaultDt !clsOuterScope =
  mkHostClass clsOuterScope "DbArray" (allocEdhObj arrayAllocator) []
    $ \ !clsScope -> do
        !mths <-
          sequence
          $  [ (AttrByName nm, ) <$> mkHostProc clsScope vc nm hp
             | (nm, vc, hp) <-
               [ ("[]"      , EdhMethod, wrapHostProc aryIdxReadProc)
               , ("[=]"     , EdhMethod, wrapHostProc aryIdxWriteProc)
               , ("__repr__", EdhMethod, wrapHostProc aryReprProc)
               ]
             ]
          ++ [ (AttrByName nm, ) <$> mkHostProperty clsScope nm getter setter
             | (nm, getter, setter) <-
               [ ("dir"  , aryDirGetter  , Nothing)
               , ("path" , aryPathGetter , Nothing)
               , ("dtype", aryDtypeGetter, Nothing)
               , ("size" , arySizeGetter , Nothing)
               , ("shape", aryShapeGetter, Nothing)
               , ("len1d", aryLen1dGetter, Just aryLen1dSetter)
               ]
             ]
        iopdUpdate mths $ edh'scope'entity clsScope

 where

  -- | host constructor DbArray(dataDir, dataPath, dtype=float64, shape=None)
  arrayAllocator
    :: "dataDir" !: Text
    -> "dataPath" !: Text
    -> "dtype" ?: Object
    -> "shape" ?: EdhValue
    -> EdhObjectAllocator
  arrayAllocator (mandatoryArg -> !dataDir) (mandatoryArg -> !dataPath) (defaultArg defaultDt -> !dto) (optionalArg -> !maybeShape) !ctorExit !etsCtor
    = if edh'in'tx etsCtor
      then throwEdh etsCtor
                    UsageError
                    "you don't create Array within a transaction"
      else castObjectStore dto >>= \case
        Nothing       -> throwEdh etsCtor UsageError "invalid dtype"
        Just (_, !dt) -> case data'type'proxy dt of
          DeviceDataType{} -> if dataDir == "" || dataPath == ""
            then throwEdh etsCtor UsageError "missing dataDir/dataPath"
            else newEmptyTMVar >>= \ !asVar -> case maybeShape of
              Nothing -> runEdhTx etsCtor $ edhContIO $ do
                mmapDbArray asVar dataDir dataPath dt Nothing
                atomically $ ctorExit $ HostStore
                  (toDyn $ DbArray dataDir dataPath dt asVar)
              Just !shapeVal ->
                parseArrayShape etsCtor shapeVal $ \ !shape ->
                  runEdhTx etsCtor $ edhContIO $ do
                    mmapDbArray asVar dataDir dataPath dt $ Just shape
                    atomically $ ctorExit $ HostStore $ toDyn $ DbArray
                      dataDir
                      dataPath
                      dt
                      asVar
          HostDataType{} ->
            throwEdh etsCtor UsageError
              $  "can not mmap as host dtype: "
              <> data'type'identifier dt


  aryDirGetter :: EdhHostProc
  aryDirGetter !exit !ets = withThisHostObj ets
    $ \ !ary -> exitEdh ets exit $ EdhString $ db'array'dir ary

  aryPathGetter :: EdhHostProc
  aryPathGetter !exit !ets = withThisHostObj ets
    $ \ !ary -> exitEdh ets exit $ EdhString $ db'array'path ary

  aryDtypeGetter :: EdhHostProc
  aryDtypeGetter !exit !ets = withThisHostObj ets $ \ !ary ->
    exitEdh ets exit $ EdhString $ data'type'identifier $ db'array'dtype ary

  arySizeGetter :: EdhHostProc
  arySizeGetter !exit !ets = withThisHostObj ets $ \(DbArray _ _ _ !das) ->
    readTMVar das >>= \case
      Right (!shape, _, _) ->
        exitEdh ets exit $ EdhDecimal $ fromIntegral $ dbArraySize shape
      Left !err -> throwSTM err

  aryShapeGetter :: EdhHostProc
  aryShapeGetter !exit !ets = withThisHostObj ets $ \(DbArray _ _ _ !das) ->
    readTMVar das >>= \case
      Right (!shape, _, _) -> exitEdh ets exit $ edhArrayShape shape
      Left  !err           -> throwSTM err

  aryLen1dGetter :: EdhHostProc
  aryLen1dGetter !exit !ets = withThisHostObj ets $ \(DbArray _ _ _ !das) ->
    readTMVar das >>= \case
      Right (_, !hdrPtr, _) ->
        unsafeIOToSTM (readDbArrayLength hdrPtr)
          >>= exitEdh ets exit
          .   EdhDecimal
          .   fromIntegral
      Left !err -> throwSTM err

  aryLen1dSetter :: Maybe EdhValue -> EdhHostProc
  aryLen1dSetter Nothing _ !ets =
    throwEdh ets UsageError "you don't delete len1d property"
  aryLen1dSetter (Just (EdhDecimal !newLen1dNum)) !exit !ets =
    case D.decimalToInteger newLen1dNum of
      Nothing -> throwEdh ets UsageError $ "bad len1d value: " <> T.pack
        (show newLen1dNum)
      Just !newLen1d -> withThisHostObj ets $ \(DbArray _ _ _ !das) ->
        readTMVar das >>= \case
          Right (_, !hdrPtr, _) -> do
            unsafeIOToSTM (writeDbArrayLength hdrPtr $ fromInteger newLen1d)
            exitEdh ets exit $ EdhDecimal $ fromInteger newLen1d
          Left !err -> throwSTM err
  aryLen1dSetter (Just !badLen1dVal) _ !ets = edhValueDesc ets badLen1dVal
    $ \ !badDesc -> throwEdh ets UsageError $ "bad len1d value: " <> badDesc

  aryReprProc :: EdhHostProc
  aryReprProc !exit !ets =
    withThisHostObj ets $ \(DbArray !dir !path !dt !das) ->
      readTMVar das >>= \case
        Left !err -> throwSTM err
        Right (!shape, _, _) ->
          exitEdh ets exit
            $  EdhString
            $  "DbArray("
            <> T.pack (show dir)
            <> ", "
            <> T.pack (show path)
            <> ", dtype="
            <> (data'type'identifier dt)
            <> ", shape="
            <> T.pack (show shape)
            <> ")"


  aryIdxReadProc :: EdhValue -> EdhHostProc
  aryIdxReadProc !idxVal !exit !ets =
    withThisHostObj ets $ \(DbArray _ _ !dt !das) -> readTMVar das >>= \case
      Left  !err             -> throwSTM err
      Right (!shape, _, !fa) -> case edhUltimate idxVal of
        -- TODO support slicing, of coz need to tell a slicing index from
        --      an element index first
        EdhArgsPack (ArgsPack !idxs _) ->
          flatIndexInShape ets idxs shape $ \ !flatIdx ->
            flat'array'read dt ets fa flatIdx $ \ !rv -> exitEdh ets exit rv
        !idx -> flatIndexInShape ets [idx] shape $ \ !flatIdx ->
          flat'array'read dt ets fa flatIdx $ \ !rv -> exitEdh ets exit rv


  aryIdxWriteProc :: EdhValue -> "toVal" ?: EdhValue -> EdhHostProc
  aryIdxWriteProc !idxVal (optionalArg -> !maybeToVal) !exit !ets =
    case maybeToVal of
      Nothing  -> throwEdh ets UsageError "you can not delete array content"
      Just !dv -> withThisHostObj ets $ \(DbArray _ _ !dt !das) ->
        readTMVar das >>= \case
          Left  !err            -> throwSTM err
          Right (!shape, _, fa) -> case edhUltimate idxVal of
            -- TODO support slicing assign, of coz need to tell a slicing index
            --      from an element index first
            EdhArgsPack (ArgsPack !idxs _) ->
              flatIndexInShape ets idxs shape $ \ !flatIdx ->
                flat'array'write dt ets fa flatIdx dv
                  $ \ !rv -> exitEdh ets exit rv
            !idx -> flatIndexInShape ets [idx] shape $ \ !flatIdx ->
              flat'array'write dt ets fa flatIdx dv
                $ \ !rv -> exitEdh ets exit rv

