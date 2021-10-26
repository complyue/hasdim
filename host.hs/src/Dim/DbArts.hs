module Dim.DbArts where

-- import           Debug.Trace

import Control.Applicative
import Control.Concurrent.STM
import Control.Monad
import Control.Monad.IO.Class
import Data.Dynamic
import qualified Data.Lossless.Decimal as D
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as T
import Data.Unique
import Dim.Column
import Dim.DbArray
import Dim.DiskBack
import Dim.FlatArray
import Event.Analytics.EHI
import Foreign hiding (void)
import Language.Edh.EHI
import Prelude

createDbArrayClass :: Object -> Object -> Edh Object
createDbArrayClass !clsColumn !defaultDt =
  mkEdhClass "DbArray" (allocObjM arrayAllocator) [] $ do
    !mths <-
      sequence $
        [ (AttrByName nm,) <$> mkEdhProc vc nm hp
          | (nm, vc, hp) <-
              [ ("__init__", EdhMethod, wrapEdhProc col__init__),
                ("__len__", EdhMethod, wrapEdhProc aryLen1dGetter),
                ("__mark__", EdhMethod, wrapEdhProc aryLen1dSetter),
                ("__repr__", EdhMethod, wrapEdhProc aryReprProc),
                ("__show__", EdhMethod, wrapEdhProc aryShowProc),
                ("([])", EdhMethod, wrapEdhProc aryIdxReadProc),
                ("([=])", EdhMethod, wrapEdhProc aryIdxWriteProc),
                ("(@<-)", EdhMethod, wrapEdhProc aryDeleAttrProc),
                ("asColumn", EdhMethod, wrapEdhProc aryAsColProc)
              ]
        ]
          ++ [ (AttrByName nm,) <$> mkEdhProperty nm getter setter
               | (nm, getter, setter) <-
                   [ ("dir", aryDirGetter, Nothing),
                     ("path", aryPathGetter, Nothing),
                     ("dtype", aryDtypeGetter, Nothing),
                     ("size", arySizeGetter, Nothing),
                     ("shape", aryShapeGetter, Nothing),
                     ("len1d", aryLen1dGetter, Just aryLen1dSetter)
                   ]
             ]
    !clsScope <- contextScope . edh'context <$> edhThreadState
    iopdUpdateEdh mths $ edh'scope'entity clsScope
  where
    arrayAllocator ::
      "dataDir" !: Text ->
      "dataPath" !: Text ->
      "dtype" ?: Object ->
      "shape" ?: EdhValue ->
      "overwrite" ?: Bool ->
      ArgsPack -> -- allow/ignore arbitrary ctor args for descendant classes
      Edh (Maybe Unique, ObjectStore)
    arrayAllocator
      (mandatoryArg -> !dataDir)
      (mandatoryArg -> !dataPath)
      (defaultArg defaultDt -> !dto)
      (optionalArg -> !maybeShape)
      (defaultArg False -> overwrite)
      _ctorOtherArgs = withDataType dto $ \case
        DeviceDt (_dt :: DeviceDataType a) -> case maybeShape of
          Nothing ->
            liftIO $ goMemMap @a Nothing
          Just !shapeVal ->
            liftIO . goMemMap @a . Just =<< parseArrayShape shapeVal
        _ ->
          throwEdhM UsageError "DbArray only works with device dtype"
        where
          goMemMap ::
            forall a.
            (Eq a, Storable a, EdhXchg a, Typeable a) =>
            Maybe ArrayShape ->
            IO (Maybe Unique, ObjectStore)
          goMemMap !mmapShape = do
            !asVar <- newEmptyTMVarIO
            mmapDbArray @a asVar dataDir dataPath mmapShape overwrite
            atomically $
              readTMVar asVar >>= \case
                Left !err -> throwSTM err
                Right {} ->
                  return
                    ( Nothing,
                      HostStore $ toDyn $ DbArray dataDir dataPath asVar
                    )

    col__init__ ::
      "dataDir" !: Text ->
      "dataPath" !: Text ->
      "dtype" ?: Object ->
      "shape" ?: EdhValue ->
      ArgsPack -> -- allow/ignore arbitrary ctor args for descendant classes
      Edh EdhValue
    col__init__
      _dataDir
      _dataPath
      (defaultArg defaultDt -> !dto)
      _maybeShape
      _ctorOtherArgs = do
        !ets <- edhThreadState
        let scope = contextScope $ edh'context ets
            this = edh'scope'this scope
            that = edh'scope'that scope

            extendsDt :: [Object] -> Edh ()
            extendsDt [] = return ()
            extendsDt (o : rest) = do
              modifyTVarEdh' (edh'obj'supers o) (++ [dto])
              if o == this
                then return ()
                else extendsDt rest

        supers <- readTVarEdh $ edh'obj'supers that
        extendsDt $ that : supers
        return nil

    aryDirGetter :: Edh EdhValue
    aryDirGetter = withDbArraySelf $ \_dbaObj !dba ->
      return $ EdhString $ db'array'dir dba

    aryPathGetter :: Edh EdhValue
    aryPathGetter = withDbArraySelf $ \_dbaObj !dba ->
      return $ EdhString $ db'array'path dba

    aryDtypeGetter :: Edh EdhValue
    aryDtypeGetter = do
      !this <- edh'scope'this . contextScope . edh'context <$> edhThreadState
      EdhObject <$> getDbArrayDtype this

    arySizeGetter :: Edh EdhValue
    arySizeGetter = withDbArraySelf $ \_dbaObj !dba ->
      readTMVarEdh (db'array'store dba) >>= \case
        Left !err -> throwHostM err
        Right (!shape, _, _) ->
          return $ EdhDecimal $ fromIntegral $ dbArraySize shape

    aryShapeGetter :: Edh EdhValue
    aryShapeGetter = withDbArraySelf $ \_dbaObj !dba ->
      readTMVarEdh (db'array'store dba) >>= \case
        Left !err -> throwHostM err
        Right (!shape, _, _) -> return $ edhArrayShape shape

    aryLen1dGetter :: Edh EdhValue
    aryLen1dGetter = withDbArraySelf $ \_dbaObj !dba ->
      readTMVarEdh (db'array'store dba) >>= \case
        Left !err -> throwHostM err
        Right (_, !hdrPtr, _) -> do
          !len1d <- liftIO $ readDbArrayLength hdrPtr
          return $ EdhDecimal $ fromIntegral len1d

    aryLen1dSetter :: Maybe EdhValue -> Edh EdhValue
    aryLen1dSetter Nothing =
      throwEdhM UsageError "you don't delete len1d property"
    aryLen1dSetter (Just (EdhDecimal !newLen1dNum)) =
      withDbArraySelf $ \_dbaObj !dba ->
        readTMVarEdh (db'array'store dba) >>= \case
          Left !err -> throwHostM err
          Right (!shape, _, _) -> case D.decimalToInteger newLen1dNum of
            Just !newLen1d
              | newLen1d >= 0 && fromIntegral newLen1d <= dbArraySize shape ->
                readTMVarEdh (db'array'store dba) >>= \case
                  Right (_, !hdrPtr, _) -> do
                    liftIO $
                      writeDbArrayLength hdrPtr $ fromInteger newLen1d
                    return $ EdhDecimal $ fromInteger newLen1d
                  Left !err -> throwHostM err
            _ ->
              throwEdhM UsageError $
                "bad len1d value " <> T.pack (show newLen1dNum)
                  <> " vs array capacity "
                  <> T.pack (show $ dbArraySize shape)
    aryLen1dSetter (Just !badLen1dVal) = do
      !badDesc <- edhSimpleDescM badLen1dVal
      throwEdhM UsageError $ "bad len1d value: " <> badDesc

    aryRepr :: forall a. Object -> DbArray a -> Edh Text
    aryRepr !dbaObj (DbArray !dir !path !das) = do
      !dto <- getDbArrayDtype dbaObj
      !dtRepr <- edhValueReprM (EdhObject dto)
      readTMVarEdh das >>= \case
        Left !err -> throwHostM err
        Right (!shape, _, _) ->
          return $
            "DbArray( "
              <> T.pack (show dir)
              <> ", "
              <> T.pack (show path)
              <> ", dtype="
              <> dtRepr
              <> ", shape="
              <> T.pack (show shape)
              <> " )"

    aryReprProc :: Edh EdhValue
    aryReprProc = withDbArraySelf $ \ !dbaObj !dba ->
      EdhString <$> aryRepr dbaObj dba

    aryShowProc :: Edh EdhValue
    aryShowProc = withDbArraySelf $ \ !dbaObj !dba ->
      readTMVarEdh (db'array'store dba) >>= \case
        Left !err -> throwHostM err
        Right (_, !hdrPtr, !fa) -> do
          !dbaRepr <- aryRepr dbaObj dba
          !len1d <- liftIO $ fromIntegral <$> readDbArrayLength hdrPtr
          let readElem i = do
                !hv <- liftIO $ array'reader fa i
                toEdh hv >>= edhValueStrM

          !contentLines <- showColContent len1d readElem
          return $ EdhString $ dbaRepr <> "\n" <> contentLines

    aryIdxReadProc :: EdhValue -> Edh EdhValue
    aryIdxReadProc !idxVal = withDbArraySelf $ \_dbaObj (DbArray _ _ !das) ->
      readTMVarEdh das >>= \case
        Left !err -> throwHostM err
        Right (!shape, _, !fa) -> do
          let exitAt :: Int -> Edh EdhValue
              exitAt flatIdx =
                -- TODO validate against len1d/cap of the array
                liftIO (array'reader fa flatIdx) >>= toEdh
          exitAt =<< case edhUltimate idxVal of
            -- TODO support slicing, of coz need to tell a slicing index from
            --      an element index first
            EdhArgsPack (ArgsPack !idxs _) ->
              flatIndexInShape idxs shape
            !idx ->
              flatIndexInShape [idx] shape

    aryIdxWriteProc :: EdhValue -> "toVal" ?: EdhValue -> Edh EdhValue
    aryIdxWriteProc !idxVal (optionalArg -> !maybeToVal) =
      withDbArraySelf $ \_dbaObj (DbArray _ _ !das) ->
        case maybeToVal of
          Nothing ->
            throwEdhM UsageError "you can not delete DbArray content"
          Just !v ->
            readTMVarEdh das >>= \case
              Left !err -> throwHostM err
              Right (!shape, _, fa) -> do
                let writeAt :: Int -> Edh EdhValue
                    writeAt flatIdx = do
                      !hv <- fromEdh v
                      liftIO $ array'writer fa flatIdx hv
                      -- convert the host value back to Edh and return it, so
                      -- truncations e.g. fractional number to floating point,
                      -- will be visible
                      toEdh hv

                writeAt =<< case edhUltimate idxVal of
                  -- TODO support slicing assign, of coz need to tell a slicing
                  --      index from an element index first
                  EdhArgsPack (ArgsPack !idxs _) ->
                    flatIndexInShape idxs shape
                  !idx ->
                    flatIndexInShape [idx] shape

    -- this is the super magic to intercept descendant object's attribute reads
    aryDeleAttrProc :: "attrKey" !: EdhValue -> Edh EdhValue
    aryDeleAttrProc (mandatoryArg -> !attrKey) = case attrKey of
      EdhString "__repr__" -> withDbArraySelf $ \ !dbaObj !dba ->
        aryRepr dbaObj dba >>= \ !dbaRepr ->
          return $ EdhString $ dbaRepr <> ".asColumn()"
      _ -> return edhNA

    aryAsColProc :: Edh EdhValue
    aryAsColProc = withDbArraySelf $ \ !dbaObj !dba -> do
      !dbaSupers <- -- by far by design, there is only the dtype inside
        readTVarEdh $ edh'obj'supers dbaObj
      EdhObject
        <$> createHostObjectM'
          clsColumn
          (toDyn $ someColumn $ DbColumn dba 0)
          -- inherit prototype based supers, including the dtype
          (dbaObj : dbaSupers)
