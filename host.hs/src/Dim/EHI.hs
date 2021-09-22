module Dim.EHI
  ( installDimBatteries,
    getColumnClass,
    getPredefinedDtype,
    getPredefinedDtype',
    createColumnObject,
    module Dim.XCHG,
    module Dim.DataType,
    module Dim.Column,
    module Dim.Fold,
    module Dim.InMem,
    module Dim.Table,
    module Dim.ColDtArts,
    module Dim.DbArray,
    module Dim.FlatArray,
  )
where

-- import           Debug.Trace

import Control.Monad.Reader
import Data.Dynamic
import Data.Lossless.Decimal as D
import Data.Maybe
import qualified Data.Text as T
import Data.Typeable hiding (TypeRep, typeOf, typeRep)
import Dim.ColArts
import Dim.ColDtArts
import Dim.Column
import Dim.DataType
import Dim.DbArray
import Dim.DbArts
import Dim.FlatArray
import Dim.Float
import Dim.Fold
import Dim.InMem
import Dim.Table
import Dim.XCHG
import Foreign hiding (void)
import Language.Edh.MHI
import Type.Reflection
import Prelude

builtinDataTypes :: Edh [(DataTypeIdent, Object)]
builtinDataTypes = do
  yesno <- mkYesNoColDt "yesno"
  box <- mkBoxColDt "box" edhNA
  decimal <- mkRealFracColDt @Decimal yesno "decimal" D.nan (Just id)
  float64 <- mkFloatColDt @Double yesno "float64"
  float32 <- mkFloatColDt @Float yesno "float32"
  int64 <- mkIntColDt @Int64 yesno "int64"
  int32 <- mkIntColDt @Int32 yesno "int32"
  int8 <- mkIntColDt @Int8 yesno "int8"
  intp <- mkIntColDt @Int yesno "intp"

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
  !moduDtypes <- installEdhModuleM world "dim/dtypes" $ do
    !moduScope <- contextScope . edh'context <$> edhThreadState

    !dtAlias <- builtinDataTypes

    let !moduArts = [(AttrByName k, EdhObject dto) | (k, dto) <- dtAlias]

    iopdUpdateEdh moduArts $ edh'scope'entity moduScope
    !esExps <- prepareExpStoreM (edh'scope'this moduScope)
    iopdUpdateEdh moduArts esExps

  void $
    installEdhModuleM world "dim/primitive/ops" $ do
      !moduScope <- contextScope . edh'context <$> edhThreadState

      !moduArts0 <-
        sequence $
          [ (AttrByName nm,) <$> def nm
            | (nm, def) <-
                [ ("fold", defineComputMethod foldComput),
                  ("foldl", defineComputMethod foldlComput),
                  ("foldr", defineComputMethod foldrComput),
                  ("scanl", defineComputMethod scanlComput),
                  ("scanr", defineComputMethod scanrComput)
                ]
          ]

      !moduArts1 <-
        sequence
          [ (AttrByName "add",) . EdhObject
              <$> wrapM' "add" (FoldOp FoldingAdd),
            (AttrByName "add'valid",) . EdhObject
              <$> wrapM' "add'valid" (FoldOp FoldingAddV),
            (AttrByName "multiply",) . EdhObject
              <$> wrapM' "multiply" (FoldOp FoldingMul),
            (AttrByName "multiply'valid",) . EdhObject
              <$> wrapM' "multiply'valid" (FoldOp FoldingMulV)
          ]

      let !moduArts = moduArts0 ++ moduArts1

      iopdUpdateEdh moduArts $ edh'scope'entity moduScope
      prepareExpStoreM (edh'scope'this moduScope) >>= \ !esExps ->
        iopdUpdateEdh moduArts esExps

  void $
    installEdhModuleM world "dim/RT" $ do
      !moduScope <- contextScope . edh'context <$> edhThreadState
      let !dtypesModuStore = case edh'obj'store moduDtypes of
            HashStore !hs -> hs
            _ -> error "bug: module not bearing hash store"

      {- HLINT ignore "Redundant <$>" -}
      !defaultDataType <-
        fromJust <$> iopdLookupEdh (AttrByName "float64") dtypesModuStore >>= \case
          EdhObject !dto -> return dto
          _ -> error "bug: dtype not object"
      !dtIntp <-
        fromJust <$> iopdLookupEdh (AttrByName "intp") dtypesModuStore >>= \case
          EdhObject !dto -> return dto
          _ -> error "bug: dtype not object"
      !dtBox <-
        fromJust <$> iopdLookupEdh (AttrByName "box") dtypesModuStore >>= \case
          EdhObject !dto -> return dto
          _ -> error "bug: dtype not object"
      let !defaultRangeDataType = dtIntp

      !clsColumn <- createColumnClass defaultDataType
      !tableClass <- createTableClass dtBox clsColumn
      !dbArrayClass <- createDbArrayClass clsColumn defaultDataType

      !moduArts0 <-
        sequence $
          [ (AttrByName nm,) <$> mkEdhProc mc nm hp
            | (mc, nm, hp) <-
                [ ( EdhMethod,
                    "arange",
                    wrapEdhProc $ arangeProc defaultRangeDataType clsColumn
                  ),
                  ( EdhMethod,
                    "random",
                    wrapEdhProc $ randomProc defaultDataType clsColumn
                  ),
                  ( EdhMethod,
                    "where",
                    wrapEdhProc $ whereProc clsColumn dtIntp
                  ),
                  ( EdhMethod,
                    "pi",
                    wrapEdhProc $ piProc defaultDataType clsColumn
                  ),
                  (EdhMethod, "exp", wrapEdhProc $ floatOpProc exp),
                  (EdhMethod, "log", wrapEdhProc $ floatOpProc log),
                  (EdhMethod, "sqrt", wrapEdhProc $ floatOpProc sqrt),
                  (EdhMethod, "sin", wrapEdhProc $ floatOpProc sin),
                  (EdhMethod, "cos", wrapEdhProc $ floatOpProc cos),
                  (EdhMethod, "tan", wrapEdhProc $ floatOpProc tan),
                  (EdhMethod, "asin", wrapEdhProc $ floatOpProc asin),
                  (EdhMethod, "acos", wrapEdhProc $ floatOpProc acos),
                  (EdhMethod, "atan", wrapEdhProc $ floatOpProc atan),
                  (EdhMethod, "sinh", wrapEdhProc $ floatOpProc sinh),
                  (EdhMethod, "cosh", wrapEdhProc $ floatOpProc cosh),
                  (EdhMethod, "tanh", wrapEdhProc $ floatOpProc tanh),
                  (EdhMethod, "asinh", wrapEdhProc $ floatOpProc asinh),
                  (EdhMethod, "acosh", wrapEdhProc $ floatOpProc acosh),
                  (EdhMethod, "atanh", wrapEdhProc $ floatOpProc atanh)
                ]
          ]

      let !moduArts =
            moduArts0
              ++ [ (AttrByName "Column", EdhObject clsColumn),
                   (AttrByName "Table", EdhObject tableClass),
                   (AttrByName "DbArray", EdhObject dbArrayClass)
                 ]
      iopdUpdateEdh moduArts $ edh'scope'entity moduScope
      prepareExpStoreM (edh'scope'this moduScope) >>= \ !esExps ->
        iopdUpdateEdh moduArts esExps

getColumnClass :: Edh Object
getColumnClass =
  importModuleM "dim/RT" >>= \ !moduRT ->
    getObjPropertyM moduRT (AttrByName "Column") >>= \case
      EdhObject !clsColumn -> return clsColumn
      _ -> naM "bug: dim/RT provides no Column class"

getPredefinedDtype :: AttrName -> Edh Object
getPredefinedDtype !dti =
  importModuleM "dim/dtypes" >>= \ !moduDtypes ->
    getObjPropertyM moduDtypes (AttrByName dti) >>= \case
      EdhObject !clsDtype -> return clsDtype
      _ -> naM $ "dim/dtypes provides no `" <> dti <> "` dtype"

getPredefinedDtype' ::
  forall a. (Typeable a) => AttrName -> Edh (DataType a, Object)
getPredefinedDtype' !dti =
  importModuleM "dim/dtypes" >>= \ !moduDtypes ->
    getObjPropertyM moduDtypes (AttrByName dti) >>= \case
      EdhObject !dto -> withDataType dto $ \(gdt :: DataType a') ->
        case eqT of
          Nothing ->
            naM $
              "requested dtype " <> dti <> " not compatible with host type: "
                <> T.pack (show $ typeRep @a)
          Just (Refl :: a' :~: a) -> return (gdt, dto)
      _ -> naM $ "dim/dtypes provides no `" <> dti <> "` dtype"

createColumnObject :: Object -> SomeColumn -> Object -> Edh Object
createColumnObject !clsColumn !col !dto =
  createHostObjectM' clsColumn (toDyn col) [dto]
