module Dim.DbArts where

-- import           Debug.Trace

{-

import Control.Concurrent.STM
  ( STM,
    atomically,
    newEmptyTMVarIO,
    readTMVar,
    throwSTM,
  )
import Data.Dynamic (toDyn)
import qualified Data.Lossless.Decimal as D
import Data.Text (Text)
import qualified Data.Text as T
import Dim.Column
import Dim.DataType
import Dim.DbArray
import Dim.DiskBack
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.EHI
import Prelude

createDbArrayClass :: Object -> Object -> Scope -> STM Object
createDbArrayClass !clsColumn !defaultDt !clsOuterScope =
  mkHostClass clsOuterScope "DbArray" (allocEdhObj arrayAllocator) [] $
    \ !clsScope -> do
      !mths <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc clsScope vc nm hp
            | (nm, vc, hp) <-
                [ ("__len__", EdhMethod, wrapHostProc aryLen1dGetter),
                  ("__mark__", EdhMethod, wrapHostProc aryLen1dSetter),
                  ("([])", EdhMethod, wrapHostProc aryIdxReadProc),
                  ("([=])", EdhMethod, wrapHostProc aryIdxWriteProc),
                  ("__repr__", EdhMethod, wrapHostProc aryReprProc),
                  ("__show__", EdhMethod, wrapHostProc aryShowProc),
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
      !etsCtor =
        castObjectStore dto >>= \case
          Nothing -> throwEdh etsCtor UsageError "invalid dtype"
          Just (_, !dt) -> case data'type'proxy dt of
            DeviceDataType {} -> case maybeShape of
              Nothing -> runEdhTx etsCtor $ edhContIO $ goMemMap dt Nothing
              Just !shapeVal -> parseArrayShape etsCtor shapeVal $
                \ !shape ->
                  runEdhTx etsCtor $ edhContIO $ goMemMap dt $ Just shape
            HostDataType {} ->
              throwEdh etsCtor UsageError $
                "can not mmap as host dtype: "
                  <> data'type'identifier dt
        where
          goMemMap :: DataType -> Maybe ArrayShape -> IO ()
          goMemMap !dt !mmapShape = do
            !asVar <- newEmptyTMVarIO
            mmapDbArray asVar dataDir dataPath dt mmapShape
            atomically $
              readTMVar asVar >>= \case
                Left !err -> throwSTM err
                Right {} ->
                  ctorExit Nothing $
                    HostStore $ toDyn $ DbArray dataDir dataPath dt asVar

    aryDirGetter :: EdhHostProc
    aryDirGetter !exit !ets = withThisHostObj ets $
      \ !ary -> exitEdh ets exit $ EdhString $ db'array'dir ary

    aryPathGetter :: EdhHostProc
    aryPathGetter !exit !ets = withThisHostObj ets $
      \ !ary -> exitEdh ets exit $ EdhString $ db'array'path ary

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
        Left !err -> throwSTM err

    aryLen1dGetter :: EdhHostProc
    aryLen1dGetter !exit !ets = withThisHostObj ets $ \(DbArray _ _ _ !das) ->
      readTMVar das >>= \case
        Right (_, !hdrPtr, _) ->
          unsafeIOToSTM (readDbArrayLength hdrPtr)
            >>= exitEdh ets exit
              . EdhDecimal
              . fromIntegral
        Left !err -> throwSTM err

    aryLen1dSetter :: Maybe EdhValue -> EdhHostProc
    aryLen1dSetter Nothing _ !ets =
      throwEdh ets UsageError "you don't delete len1d property"
    aryLen1dSetter (Just (EdhDecimal !newLen1dNum)) !exit !ets =
      case D.decimalToInteger newLen1dNum of
        Nothing ->
          throwEdh ets UsageError $
            "bad len1d value: "
              <> T.pack
                (show newLen1dNum)
        Just !newLen1d -> withThisHostObj ets $ \(DbArray _ _ _ !das) ->
          readTMVar das >>= \case
            Right (_, !hdrPtr, _) -> do
              unsafeIOToSTM (writeDbArrayLength hdrPtr $ fromInteger newLen1d)
              exitEdh ets exit $ EdhDecimal $ fromInteger newLen1d
            Left !err -> throwSTM err
    aryLen1dSetter (Just !badLen1dVal) _ !ets = edhSimpleDesc ets badLen1dVal $
      \ !badDesc -> throwEdh ets UsageError $ "bad len1d value: " <> badDesc

    aryReprProc :: EdhHostProc
    aryReprProc !exit !ets =
      withThisHostObj ets $ \(DbArray !dir !path !dt !das) ->
        readTMVar das >>= \case
          Left !err -> throwSTM err
          Right (!shape, _, _) ->
            exitEdh ets exit $
              EdhString $
                "DbArray( "
                  <> T.pack (show dir)
                  <> ", "
                  <> T.pack (show path)
                  <> ", dtype="
                  <> data'type'identifier dt
                  <> ", shape="
                  <> T.pack (show shape)
                  <> ", )"

    aryShowProc :: EdhHostProc
    aryShowProc !exit !ets =
      withThisHostObj ets $ \(DbArray _dir _path !dt !das) ->
        readTMVar das >>= \case
          Left !err -> throwSTM err
          Right (_shape, !hdr, !fa) -> do
            !len <- unsafeIOToSTM $ readDbArrayLength hdr
            showData (fromIntegral len) $ flat'array'read dt ets fa
      where
        !thisObj = edh'scope'this $ contextScope $ edh'context ets

        exitWithDetails :: Text -> STM ()
        exitWithDetails !details = edhValueRepr ets (EdhObject thisObj) $
          \ !repr -> exitEdh ets exit $ EdhString $ repr <> "\n" <> details

        showData :: Int -> (Int -> (EdhValue -> STM ()) -> STM ()) -> STM ()
        showData !len !readElem = go 0 [] 0 ""
          where
            go :: Int -> [Text] -> Int -> Text -> STM ()
            -- TODO don't generate all lines for large columns
            go !i !cumLines !lineIdx !line
              | i >= len =
                exitWithDetails $
                  if T.null line && null cumLines
                    then "Zero-Length Array"
                    else
                      "# flat length = " <> T.pack (show len) <> "\n"
                        <> if null cumLines
                          then line
                          else
                            let !fullLines =
                                  line :
                                  " # " -- todo make this tunable ?
                                    <> T.pack (show lineIdx)
                                    <> " ~ "
                                    <> T.pack (show $ i - 1) :
                                  cumLines
                                !lineCnt = length fullLines
                             in if lineCnt > 20
                                  then
                                    T.unlines $
                                      reverse $
                                        take 10 fullLines
                                          -- todo make this tunable
                                          ++ ["# ... "]
                                          ++ drop (lineCnt - 10) fullLines
                                  else T.unlines $ reverse fullLines
            go !i !cumLines !lineIdx !line = readElem i $ \ !elemVal ->
              edhValueRepr ets elemVal $ \ !elemRepr ->
                let !tentLine = line <> elemRepr <> ", "
                 in if T.length tentLine > 79 -- todo make this tunable ?
                      then
                        go
                          (i + 1)
                          ( line :
                            ( " # " -- todo make this tunable ?
                                <> T.pack (show lineIdx)
                                <> " ~ "
                                <> T.pack (show $ i - 1)
                            ) :
                            cumLines
                          )
                          i
                          (elemRepr <> ", ")
                      else go (i + 1) cumLines lineIdx tentLine

    aryIdxReadProc :: EdhValue -> EdhHostProc
    aryIdxReadProc !idxVal !exit !ets =
      withThisHostObj ets $ \(DbArray _ _ !dt !das) ->
        readTMVar das >>= \case
          Left !err -> throwSTM err
          Right (!shape, _, !fa) -> case edhUltimate idxVal of
            -- TODO support slicing, of coz need to tell a slicing index from
            --      an element index first
            EdhArgsPack (ArgsPack !idxs _) ->
              flatIndexInShape ets idxs shape $ \ !flatIdx ->
                flat'array'read dt ets fa flatIdx $ \ !rv ->
                  exitEdh ets exit rv
            !idx -> flatIndexInShape ets [idx] shape $ \ !flatIdx ->
              flat'array'read dt ets fa flatIdx $ \ !rv -> exitEdh ets exit rv

    aryIdxWriteProc :: EdhValue -> "toVal" ?: EdhValue -> EdhHostProc
    aryIdxWriteProc !idxVal (optionalArg -> !maybeToVal) !exit !ets =
      case maybeToVal of
        Nothing -> throwEdh ets UsageError "you can not delete array content"
        Just !dv -> withThisHostObj ets $ \(DbArray _ _ !dt !das) ->
          readTMVar das >>= \case
            Left !err -> throwSTM err
            Right (!shape, _, fa) -> case edhUltimate idxVal of
              -- TODO support slicing assign, of coz need to tell a slicing
              --      index from an element index first
              EdhArgsPack (ArgsPack !idxs _) ->
                flatIndexInShape ets idxs shape $ \ !flatIdx ->
                  flat'array'write dt ets fa flatIdx dv $
                    \ !rv -> exitEdh ets exit rv
              !idx -> flatIndexInShape ets [idx] shape $ \ !flatIdx ->
                flat'array'write dt ets fa flatIdx dv $
                  \ !rv -> exitEdh ets exit rv

    -- this is the super magic to intercept descendant object's attribute reads
    aryDeleAttrProc :: "attrKey" !: EdhValue -> EdhHostProc
    aryDeleAttrProc (mandatoryArg -> !attrKey) !exit !ets = case attrKey of
      EdhString "__repr__" | edh'obj'class thatObj == clsColumn ->
        runEdhTx ets $
          aryReprProc $ \case
            EdhString !dbaRepr ->
              exitEdhTx exit $ EdhString $ dbaRepr <> ".asColumn()"
            _ -> throwEdhTx EvalError "bug: aryReprProc returned non-string"
      _ -> exitEdh ets exit edhNA
      where
        !thatObj = edh'scope'that $ contextScope $ edh'context ets

    aryAsColProc :: EdhHostProc
    aryAsColProc !exit !ets = withThisHostObj ets $ \dba@DbArray {} ->
      edhCreateHostObj' clsColumn (toDyn $ Column $ DbColumn dba 0) [thatObj]
        >>= exitEdh ets exit . EdhObject
      where
        !thatObj = edh'scope'that $ contextScope $ edh'context ets

-}
