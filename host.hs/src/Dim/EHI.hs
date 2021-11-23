module Dim.EHI
  ( installDimBatteries,
    getColumnClass,
    getPredefinedDtype,
    getPredefinedDtype',
    createColumnObject,
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

import Control.Monad
import Data.Dynamic
import Data.Lossless.Decimal as D
import Data.Maybe
import qualified Data.Text as T
import Data.Typeable hiding (TypeRep, typeOf, typeRep)
import Dim.ColArts
import Dim.ColDtArts
import Dim.Column
import Dim.DbArray
import Dim.DbArts
import Dim.FlatArray
import Dim.Float
import Dim.Fold
import Dim.InMem
import Dim.Table
import Event.Analytics.EHI
import Foreign hiding (void)
import Language.Edh.EHI
import Type.Reflection
import Prelude

installDimBatteries :: EdhWorld -> IO ()
installDimBatteries !world = runProgramM_ world $ do
  yesno <- mkYesNoColDt "yesno"
  box <- mkBoxColDt "box" edhNA
  decimal <- mkRealFracColDt @Decimal yesno "decimal" D.nan (Just id)
  float64 <- mkFloatColDt @Double yesno "float64"
  float32 <- mkFloatColDt @Float yesno "float32"
  int64 <- mkIntColDt @Int64 yesno "int64"
  int32 <- mkIntColDt @Int32 yesno "int32"
  int8 <- mkIntColDt @Int8 yesno "int8"
  intp <- mkIntColDt @Int yesno "intp"

  installModuleM_ "dim/dtypes" $
    exportM_ $ do
      defEdhArt "yesno" $ EdhObject yesno
      defEdhArt "box" $ EdhObject box
      defEdhArt "decimal" $ EdhObject decimal
      defEdhArt "float64" $ EdhObject float64
      defEdhArt "f8" $ EdhObject float64
      defEdhArt "float32" $ EdhObject float32
      defEdhArt "f4" $ EdhObject float32
      defEdhArt "int64" $ EdhObject int64
      defEdhArt "i8" $ EdhObject int64
      defEdhArt "int32" $ EdhObject int32
      defEdhArt "i4" $ EdhObject int32
      defEdhArt "int8" $ EdhObject int8
      defEdhArt "byte" $ EdhObject int8
      defEdhArt "intp" $ EdhObject intp
      defEdhArt "bool" $ EdhObject yesno
      -- for numpy compat, not all values are objects in Edh
      defEdhArt "object" $ EdhObject box

  installModuleM_ "dim/primitive/ops" $ do
    let defFoldOp :: forall t. Typeable t => AttrName -> t -> Edh ()
        defFoldOp nm t = defEdhArt nm . EdhObject =<< wrapArbiM' nm t

    exportM_ $ do
      defineComputMethod_ "fold" foldComput
      defineComputMethod_ "foldl" foldlComput
      defineComputMethod_ "foldr" foldrComput
      defineComputMethod_ "scanl" scanlComput
      defineComputMethod_ "scanr" scanrComput

      defFoldOp "add" (FoldOp FoldingAdd)
      defFoldOp "add'valid" (FoldOp FoldingAddV)
      defFoldOp "multiply" (FoldOp FoldingMul)
      defFoldOp "multiply'valid" (FoldOp FoldingMulV)

  installModuleM_ "dim/RT" $
    exportM_ $ do
      !clsColumn <- defineColumnClass float64
      void $ defineTableClass box clsColumn
      void $ defineDbArrayClass clsColumn float64

      defEdhProc'_ EdhMethod "arange" $ arangeProc intp clsColumn
      defEdhProc'_ EdhMethod "random" $ randomProc float64 clsColumn
      defEdhProc'_ EdhMethod "where" $ whereProc clsColumn intp
      defEdhProc'_ EdhMethod "pi" $ piProc float64 clsColumn
      defEdhProc'_ EdhMethod "exp" $ floatOpProc exp
      defEdhProc'_ EdhMethod "log" $ floatOpProc log
      defEdhProc'_ EdhMethod "sqrt" $ floatOpProc sqrt
      defEdhProc'_ EdhMethod "sin" $ floatOpProc sin
      defEdhProc'_ EdhMethod "cos" $ floatOpProc cos
      defEdhProc'_ EdhMethod "tan" $ floatOpProc tan
      defEdhProc'_ EdhMethod "asin" $ floatOpProc asin
      defEdhProc'_ EdhMethod "acos" $ floatOpProc acos
      defEdhProc'_ EdhMethod "atan" $ floatOpProc atan
      defEdhProc'_ EdhMethod "sinh" $ floatOpProc sinh
      defEdhProc'_ EdhMethod "cosh" $ floatOpProc cosh
      defEdhProc'_ EdhMethod "tanh" $ floatOpProc tanh
      defEdhProc'_ EdhMethod "asinh" $ floatOpProc asinh
      defEdhProc'_ EdhMethod "acosh" $ floatOpProc acosh
      defEdhProc'_ EdhMethod "atanh" $ floatOpProc atanh

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
      EdhObject !dto -> return dto
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
  createArbiHostObjectM' clsColumn col [dto]
