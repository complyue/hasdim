module Dim.DbArts where

-- import           Debug.Trace

import Control.Concurrent.STM
import Data.Dynamic (toDyn)
import qualified Data.Lossless.Decimal as D
import Data.Text (Text)
import qualified Data.Text as T
import Dim.Column
import Dim.DataType
import Dim.DbArray
import Dim.DiskBack
import Dim.XCHG
import Foreign
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.MHI
import Type.Reflection
import Prelude

createDbArrayClass :: Object -> Object -> Scope -> STM Object
createDbArrayClass !clsColumn !defaultDt !clsOuterScope =
  mkHostClass clsOuterScope "DbArray" (allocEdhObj arrayAllocator) [] $
    \ !clsScope -> do
      !mths <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc clsScope vc nm hp
            | (nm, vc, hp) <-
                [ ("__init__", EdhMethod, wrapHostProc col__init__),
                  ("__len__", EdhMethod, wrapHostProc aryLen1dGetter),
                  ("__mark__", EdhMethod, wrapHostProc aryLen1dSetter),
                  ("__repr__", EdhMethod, wrapHostProc aryReprProc),
                  ("__show__", EdhMethod, wrapHostProc aryShowProc),
                  ("([])", EdhMethod, wrapHostProc aryIdxReadProc),
                  ("([=])", EdhMethod, wrapHostProc aryIdxWriteProc),
                  ("(@<-)", EdhMethod, wrapHostProc aryDeleAttrProc),
                  ("asColumn", EdhMethod, wrapHostProc aryAsColProc)
                ]
          ]
            ++ [ (AttrByName nm,) <$> mkHostProperty clsScope nm getter setter
                 | (nm, getter, setter) <-
                     [ ("dir", aryDirGetter, Nothing),
                       ("path", aryPathGetter, Nothing),
                       ("dtype", aryDtypeGetter, Nothing),
                       ("size", arySizeGetter, Nothing),
                       ("shape", aryShapeGetter, Nothing),
                       ("len1d", aryLen1dGetter, Just aryLen1dSetter)
                     ]
               ]
      iopdUpdate mths $ edh'scope'entity clsScope
  where
    arrayAllocator ::
      "dataDir" !: Text ->
      "dataPath" !: Text ->
      "dtype" ?: Object ->
      "shape" ?: EdhValue ->
      ArgsPack -> -- allow/ignore arbitrary ctor args for descendant classes
      EdhObjectAllocator
    arrayAllocator
      (mandatoryArg -> !dataDir)
      (mandatoryArg -> !dataPath)
      (defaultArg defaultDt -> !dto)
      (optionalArg -> !maybeShape)
      _ctorOtherArgs
      !ctorExit
      !etsCtor = withDataType dto badDtype $ \case
        DirectDt _ ->
          throwEdh etsCtor UsageError "DbArray only works with device dtype"
        DeviceDt dt -> with'device'data'type dt $
          \(_ :: TypeRep a) -> case maybeShape of
            Nothing ->
              runEdhTx etsCtor $ edhContIO $ goMemMap @a Nothing
            Just !shapeVal -> parseArrayShape etsCtor shapeVal $
              \ !shape ->
                runEdhTx etsCtor $ edhContIO $ goMemMap @a $ Just shape
        where
          badDtype = edhSimpleDesc etsCtor (EdhObject dto) $ \ !badDesc ->
            throwEdh etsCtor UsageError $ "invalid dtype: " <> badDesc

          goMemMap ::
            forall a.
            (Eq a, Storable a, EdhXchg a, Typeable a) =>
            Maybe ArrayShape ->
            IO ()
          goMemMap !mmapShape = do
            !asVar <- newEmptyTMVarIO
            mmapDbArray @a asVar dataDir dataPath mmapShape
            atomically $
              readTMVar asVar >>= \case
                Left !err -> throwSTM err
                Right {} ->
                  ctorExit Nothing $
                    HostStore $ toDyn $ DbArray dataDir dataPath asVar

    col__init__ ::
      "dataDir" !: Text ->
      "dataPath" !: Text ->
      "dtype" ?: Object ->
      "shape" ?: EdhValue ->
      ArgsPack -> -- allow/ignore arbitrary ctor args for descendant classes
      EdhHostProc
    col__init__
      _dataDir
      _dataPath
      (defaultArg defaultDt -> !dto)
      _maybeShape
      _ctorOtherArgs
      !exit
      !ets = do
        supers <- readTVar $ edh'obj'supers that
        extendsDt $ that : supers
        exitEdh ets exit nil
        where
          scope = contextScope $ edh'context ets
          this = edh'scope'this scope
          that = edh'scope'that scope

          extendsDt :: [Object] -> STM ()
          extendsDt [] = return ()
          extendsDt (o : rest) = do
            modifyTVar' (edh'obj'supers o) (++ [dto])
            if o == this
              then return ()
              else extendsDt rest

    aryDirGetter :: EdhHostProc
    aryDirGetter !exit = withDbArraySelf $ \_dbaObj !dba ->
      exitEdhTx exit $ EdhString $ db'array'dir dba

    aryPathGetter :: EdhHostProc
    aryPathGetter !exit = withDbArraySelf $ \_dbaObj !dba ->
      exitEdhTx exit $ EdhString $ db'array'path dba

    aryDtypeGetter :: EdhHostProc
    aryDtypeGetter !exit !ets =
      getDbArrayDtype ets this $ exitEdh ets exit . EdhObject
      where
        scope = contextScope $ edh'context ets
        this = edh'scope'this scope

    arySizeGetter :: EdhHostProc
    arySizeGetter !exit = withDbArraySelf $ \_dbaObj !dba !ets ->
      readTMVar (db'array'store dba) >>= \case
        Left !err -> throwSTM err
        Right (!shape, _, _) ->
          exitEdh ets exit $ EdhDecimal $ fromIntegral $ dbArraySize shape

    aryShapeGetter :: EdhHostProc
    aryShapeGetter !exit = withDbArraySelf $ \_dbaObj !dba !ets ->
      readTMVar (db'array'store dba) >>= \case
        Left !err -> throwSTM err
        Right (!shape, _, _) -> exitEdh ets exit $ edhArrayShape shape

    aryLen1dGetter :: EdhHostProc
    aryLen1dGetter !exit = withDbArraySelf $ \_dbaObj !dba !ets ->
      readTMVar (db'array'store dba) >>= \case
        Left !err -> throwSTM err
        Right (_, !hdrPtr, _) -> do
          !len1d <- unsafeIOToSTM (readDbArrayLength hdrPtr)
          exitEdh ets exit $ EdhDecimal $ fromIntegral len1d

    aryLen1dSetter :: Maybe EdhValue -> EdhHostProc
    aryLen1dSetter Nothing _ =
      throwEdhTx UsageError "you don't delete len1d property"
    aryLen1dSetter (Just (EdhDecimal !newLen1dNum)) !exit =
      withDbArraySelf $ \_dbaObj !dba !ets ->
        readTMVar (db'array'store dba) >>= \case
          Left !err -> throwSTM err
          Right (!shape, _, _) -> case D.decimalToInteger newLen1dNum of
            Just !newLen1d
              | newLen1d >= 0 && fromIntegral newLen1d <= dbArraySize shape ->
                readTMVar (db'array'store dba) >>= \case
                  Right (_, !hdrPtr, _) -> do
                    unsafeIOToSTM $
                      writeDbArrayLength hdrPtr $ fromInteger newLen1d
                    exitEdh ets exit $ EdhDecimal $ fromInteger newLen1d
                  Left !err -> throwSTM err
            _ ->
              throwEdh ets UsageError $
                "bad len1d value " <> T.pack (show newLen1dNum)
                  <> " vs array capacity "
                  <> T.pack (show $ dbArraySize shape)
    aryLen1dSetter (Just !badLen1dVal) _ = edhSimpleDescTx badLen1dVal $
      \ !badDesc -> throwEdhTx UsageError $ "bad len1d value: " <> badDesc

    aryRepr :: forall a. Object -> DbArray a -> EdhTxExit Text -> EdhTx
    aryRepr !dbaObj (DbArray !dir !path !das) !exit !ets =
      getDbArrayDtype ets dbaObj $
        \ !dto -> edhValueRepr ets (EdhObject dto) $ \ !dtRepr ->
          readTMVar das >>= \case
            Left !err -> throwSTM err
            Right (!shape, _, _) ->
              exitEdh ets exit $
                "DbArray( "
                  <> T.pack (show dir)
                  <> ", "
                  <> T.pack (show path)
                  <> ", dtype="
                  <> dtRepr
                  <> ", shape="
                  <> T.pack (show shape)
                  <> " )"

    aryReprProc :: EdhHostProc
    aryReprProc !exit = withDbArraySelf $ \ !dbaObj !dba ->
      aryRepr dbaObj dba $ exit . EdhString

    aryShowProc :: EdhHostProc
    aryShowProc !exit = withDbArraySelf $ \ !dbaObj !dba !ets ->
      readTMVar (db'array'store dba) >>= \case
        Left !err -> throwSTM err
        Right (_, !hdrPtr, !fa) -> runEdhTx ets $
          aryRepr dbaObj dba $ \ !dbaRepr -> edhContIO $ do
            !len1d <- fromIntegral <$> readDbArrayLength hdrPtr
            let readElem i !elemExit = do
                  !hv <- array'reader fa i
                  atomically $
                    runEdhTx ets $
                      toEdh hv $
                        \ !v -> edhValueStrTx v $ edhContIO . elemExit
            showColContent len1d readElem $ \ !contentLines ->
              atomically $
                exitEdh ets exit $
                  EdhString $ dbaRepr <> "\n" <> contentLines

    aryIdxReadProc :: EdhValue -> EdhHostProc
    aryIdxReadProc !idxVal !exit = withDbArraySelf $
      \_dbaObj (DbArray _ _ !das) !ets -> do
        readTMVar das >>= \case
          Left !err -> throwSTM err
          Right (!shape, _, !fa) -> do
            let exitAt :: Int -> STM ()
                exitAt flatIdx = runEdhTx ets $
                  edhContIO $ do
                    -- TODO validate against len1d/cap of the array
                    !rv <- array'reader fa flatIdx
                    atomically $ runEdhTx ets $ toEdh rv exit
            case edhUltimate idxVal of
              -- TODO support slicing, of coz need to tell a slicing index from
              --      an element index first
              EdhArgsPack (ArgsPack !idxs _) ->
                flatIndexInShape ets idxs shape exitAt
              !idx ->
                flatIndexInShape ets [idx] shape exitAt

    aryIdxWriteProc :: EdhValue -> "toVal" ?: EdhValue -> EdhHostProc
    aryIdxWriteProc !idxVal (optionalArg -> !maybeToVal) !exit =
      withDbArraySelf $ \_dbaObj (DbArray _ _ !das) !ets ->
        case maybeToVal of
          Nothing ->
            throwEdh ets UsageError "you can not delete DbArray content"
          Just !v ->
            readTMVar das >>= \case
              Left !err -> throwSTM err
              Right (!shape, _, fa) -> do
                let writeAt :: Int -> STM ()
                    writeAt flatIdx = runEdhTx ets $
                      fromEdh v $ \ !hv -> edhContIO $ do
                        array'writer fa flatIdx hv
                        -- convert the host value back to Edh and return it
                        -- truncations e.g. fractional number to floating point,
                        -- will be visible
                        atomically $ runEdhTx ets $ toEdh hv exit

                case edhUltimate idxVal of
                  -- TODO support slicing assign, of coz need to tell a slicing
                  --      index from an element index first
                  EdhArgsPack (ArgsPack !idxs _) ->
                    flatIndexInShape ets idxs shape writeAt
                  !idx ->
                    flatIndexInShape ets [idx] shape writeAt

    -- this is the super magic to intercept descendant object's attribute reads
    aryDeleAttrProc :: "attrKey" !: EdhValue -> EdhHostProc
    aryDeleAttrProc (mandatoryArg -> !attrKey) !exit = case attrKey of
      EdhString "__repr__" -> withDbArraySelf $ \ !dbaObj !dba ->
        aryRepr dbaObj dba $ \ !dbaRepr ->
          exitEdhTx exit $ EdhString $ dbaRepr <> ".asColumn()"
      _ -> exitEdhTx exit edhNA

    aryAsColProc :: EdhHostProc
    aryAsColProc !exit = withDbArraySelf $ \ !dbaObj !dba !ets -> do
      !dbaSupers <- -- by far by design, only the dtype inside
        readTVar $ edh'obj'supers dbaObj
      !dbcObj <-
        edhCreateHostObj'
          clsColumn
          (toDyn $ someColumn $ DbColumn dba 0)
          -- inherit prototype based supers, including the dtype
          (dbaObj : dbaSupers)
      exitEdh ets exit $ EdhObject dbcObj
