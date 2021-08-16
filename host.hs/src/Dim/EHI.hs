module Dim.EHI
  ( installDimBatteries,
    withColumnClass,
    withYesNoDtype,
    module Dim.XCHG,
    module Dim.DataType,
    module Dim.Column,
    module Dim.InMem,
    module Dim.Table,
    module Dim.DbArray,
  )
where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Monad.Reader
import Data.Dynamic
import qualified Data.Lossless.Decimal as D
import Data.Maybe
import Dim.ColArts
import Dim.Column
import Dim.DataType
import Dim.DbArray
import Dim.DbArts
import Dim.Float
import Dim.InMem
import Dim.Table
import Dim.XCHG
import Foreign hiding (void)
import Language.Edh.EHI
import Prelude

builtinDataTypes :: Scope -> STM [(DataTypeIdent, Object)]
builtinDataTypes !moduScope = do
  yesno <- mkYesNoSuperDt "yesno" moduScope
  box <- mkBoxSuperDt "box" edhNA moduScope
  decimal <- mkRealFracSuperDt @Decimal yesno "decimal" moduScope
  float64 <- mkFloatSuperDt @Double yesno "float64" moduScope
  float32 <- mkFloatSuperDt @Float yesno "float32" moduScope
  int64 <- mkIntSuperDt @Int64 yesno "int64" moduScope
  int32 <- mkIntSuperDt @Int32 yesno "int32" moduScope
  int8 <- mkIntSuperDt @Int8 yesno "int8" moduScope
  intp <- mkIntSuperDt @Int yesno "intp" moduScope

  return
    [ ("float64", float64),
      ("f8", float64),
      ("float32", float32),
      ("f4", float32),
      ("int64", int64),
      ("i8", int64),
      ("int32", int32),
      ("i4", int32),
      ("int8", int8),
      ("byte", int8),
      ("intp", intp),
      ("yesno", yesno),
      ("bool", yesno),
      ("box", box),
      ("object", box), -- for numpy compat, not all values are objects in Edh
      ("decimal", decimal)
    ]

installDimBatteries :: EdhWorld -> IO ()
installDimBatteries !world = do
  !moduDtypes <- installEdhModule world "dim/dtypes" $ \ !ets !exit -> do
    let !moduScope = contextScope $ edh'context ets

    !dtAlias <- builtinDataTypes moduScope

    let !moduArts = [(AttrByName k, EdhObject dto) | (k, dto) <- dtAlias]

    iopdUpdate moduArts $ edh'scope'entity moduScope
    prepareExpStore ets (edh'scope'this moduScope) $ \ !esExps ->
      iopdUpdate moduArts esExps

    exit

  void $
    installEdhModule world "dim/primitive/ops" $ \ !ets !exit -> do
      let !moduScope = contextScope $ edh'context ets

      !moduArts0 <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc moduScope mc nm hp
            | (mc, nm, hp) <-
                []
          ]
      -- (EdhMethod, "fold", wrapHostProc foldOpProc)
      -- (EdhMethod, "scan", wrapHostProc scanOpProc)

      !moduArts1 <-
        sequence
          []
      {-
      (AttrByName "add",) . EdhObject <$> edhWrapHostValue ets addOp,
      (AttrByName "add'valid",) . EdhObject
        <$> edhWrapHostValue ets addValidOp,
      (AttrByName "multiply",) . EdhObject <$> edhWrapHostValue ets mulOp,
      (AttrByName "multiply'valid",) . EdhObject
        <$> edhWrapHostValue ets mulValidOp
      -}

      let !moduArts = moduArts0 ++ moduArts1

      iopdUpdate moduArts $ edh'scope'entity moduScope
      prepareExpStore ets (edh'scope'this moduScope) $ \ !esExps ->
        iopdUpdate moduArts esExps

      exit

  void $
    installEdhModule world "dim/RT" $ \ !ets !exit -> do
      let !dtypesModuStore = case edh'obj'store moduDtypes of
            HashStore !hs -> hs
            _ -> error "bug: module not bearing hash store"

      {- HLINT ignore "Redundant <$>" -}
      !defaultDataType <-
        fromJust <$> iopdLookup (AttrByName "float64") dtypesModuStore >>= \case
          EdhObject !dto -> return dto
          _ -> error "bug: dtype not object"
      !dtIntp <-
        fromJust <$> iopdLookup (AttrByName "intp") dtypesModuStore >>= \case
          EdhObject !dto -> return dto
          _ -> error "bug: dtype not object"
      let !defaultRangeDataType = dtIntp

      let !moduScope = contextScope $ edh'context ets

      !columnClass <- createColumnClass defaultDataType moduScope

      -- !tableClass <- createTableClass columnClass moduScope
      -- !dbArrayClass <- createDbArrayClass columnClass defaultDataType moduScope

      !moduArts0 <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc moduScope mc nm hp
            | (mc, nm, hp) <-
                [ ( EdhMethod,
                    "arange",
                    wrapHostProc $ arangeProc defaultRangeDataType columnClass
                  ),
                  ( EdhMethod,
                    "random",
                    wrapHostProc $ randomProc defaultDataType columnClass
                  ),
                  ( EdhMethod,
                    "where",
                    wrapHostProc $ whereProc columnClass dtIntp
                  ),
                  ( EdhMethod,
                    "pi",
                    wrapHostProc $ piProc defaultDataType columnClass
                  ),
                  (EdhMethod, "exp", wrapHostProc $ floatOpProc exp),
                  (EdhMethod, "log", wrapHostProc $ floatOpProc log),
                  (EdhMethod, "sqrt", wrapHostProc $ floatOpProc sqrt),
                  (EdhMethod, "sin", wrapHostProc $ floatOpProc sin),
                  (EdhMethod, "cos", wrapHostProc $ floatOpProc cos),
                  (EdhMethod, "tan", wrapHostProc $ floatOpProc tan),
                  (EdhMethod, "asin", wrapHostProc $ floatOpProc asin),
                  (EdhMethod, "acos", wrapHostProc $ floatOpProc acos),
                  (EdhMethod, "atan", wrapHostProc $ floatOpProc atan),
                  (EdhMethod, "sinh", wrapHostProc $ floatOpProc sinh),
                  (EdhMethod, "cosh", wrapHostProc $ floatOpProc cosh),
                  (EdhMethod, "tanh", wrapHostProc $ floatOpProc tanh),
                  (EdhMethod, "asinh", wrapHostProc $ floatOpProc asinh),
                  (EdhMethod, "acosh", wrapHostProc $ floatOpProc acosh),
                  (EdhMethod, "atanh", wrapHostProc $ floatOpProc atanh)
                ]
          ]

      let !moduArts =
            moduArts0
              ++ [ (AttrByName "Column", EdhObject columnClass)
              --  (AttrByName "Table", EdhObject tableClass),
              --  (AttrByName "DbArray", EdhObject dbArrayClass)
                 ]
      iopdUpdate moduArts $ edh'scope'entity moduScope
      prepareExpStore ets (edh'scope'this moduScope) $ \ !esExps ->
        iopdUpdate moduArts esExps

      exit

withColumnClass :: (Object -> EdhTx) -> EdhTx
withColumnClass !act = importEdhModule "dim/RT" $ \ !moduRT !ets ->
  lookupEdhObjAttr moduRT (AttrByName "Column") >>= \case
    (_, EdhObject !clsColumn) -> runEdhTx ets $ act clsColumn
    _ -> error "bug: dim/RT provides no Column class"

withYesNoDtype :: (Object -> EdhTx) -> EdhTx
withYesNoDtype !act = importEdhModule "dim/dtypes" $ \ !moduDtypes !ets ->
  lookupEdhObjAttr moduDtypes (AttrByName "yesno") >>= \case
    (_, EdhObject !clsDtype) -> runEdhTx ets $ act clsDtype
    _ -> error "bug: dim/dtypes provides no `yesno` dtype"
