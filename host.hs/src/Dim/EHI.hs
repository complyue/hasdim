module Dim.EHI
  ( installDimBatteries,
    withColumnClass,
    withDtypeClass,
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

builtinDataTypes :: Object -> STM [(DataTypeIdent, Object)]
builtinDataTypes !dtClass =
  concat
    <$> sequence
      [ mkFloatDtWithAlias @Double "float64" ["f8"],
        mkFloatDtWithAlias @Float "float32" ["f4"],
        mkIntDtWithAlias @Int64 "int64" ["i8"],
        mkIntDtWithAlias @Int32 "int32" ["i4"],
        mkIntDtWithAlias @Int8 "int8" ["byte"],
        mkIntDtWithAlias @Int "intp" [],
        mkIntDtWithAlias @YesNo "yesno" ["bool"],
        mkRealFracDtWithAlias @D.Decimal "decimal" D.nan [],
        mkBoxDtWithAlias @EdhValue
          "box"
          edhNA
          [ "object" -- for numpy compat, not all values are objects in Edh
          ]
      ]
  where
    mkIntDtWithAlias ::
      forall a.
      (Integral a, Storable a, EdhXchg a, Typeable a) =>
      DataTypeIdent ->
      [DataTypeIdent] ->
      STM [(DataTypeIdent, Object)]
    mkIntDtWithAlias !dti !alias =
      let !dt = mkIntDataType @a dti
       in edhCreateHostObj dtClass dt
            >>= \ !dto -> return $ ((dti, dto) :) $ (,dto) <$> alias
    mkFloatDtWithAlias ::
      forall a.
      (RealFloat a, Storable a, EdhXchg a, Typeable a) =>
      DataTypeIdent ->
      [DataTypeIdent] ->
      STM [(DataTypeIdent, Object)]
    mkFloatDtWithAlias !dti !alias =
      let !dt = mkFloatDataType @a dti
       in edhCreateHostObj dtClass dt
            >>= \ !dto -> return $ ((dti, dto) :) $ (,dto) <$> alias

    mkBoxDtWithAlias ::
      forall a.
      (EdhXchg a, Eq a, Typeable a) =>
      DataTypeIdent ->
      a ->
      [DataTypeIdent] ->
      STM [(DataTypeIdent, Object)]
    mkBoxDtWithAlias !dti !def'val !alias =
      let !dt = mkBoxDataType dti def'val
       in edhCreateHostObj dtClass dt
            >>= \ !dto -> return $ ((dti, dto) :) $ (,dto) <$> alias

    mkRealFracDtWithAlias ::
      forall a.
      (RealFrac a, EdhXchg a, Eq a, Typeable a) =>
      DataTypeIdent ->
      a ->
      [DataTypeIdent] ->
      STM [(DataTypeIdent, Object)]
    mkRealFracDtWithAlias !dti !def'val !alias =
      let !dt = mkRealFracDataType dti def'val
       in edhCreateHostObj dtClass dt
            >>= \ !dto -> return $ ((dti, dto) :) $ (,dto) <$> alias

installDimBatteries :: EdhWorld -> IO ()
installDimBatteries !world = do
  !moduDtypes <- installEdhModule world "dim/dtypes" $ \ !ets !exit -> do
    let !moduScope = contextScope $ edh'context ets

    -- !dtAlias <- builtinDataTypes dtClass

    let !moduArts =
          []
    -- (AttrByName k, EdhObject dto) | (k, dto) <- dtAlias

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
      -- !defaultRangeDataType <-
      --   fromJust <$> iopdLookup (AttrByName "intp") dtypesModuStore >>= \case
      --     EdhObject !dto -> return dto
      --     _ -> error "bug: dtype not object"

      let !moduScope = contextScope $ edh'context ets

      !columnClass <- createColumnClass defaultDataType moduScope

      -- !tableClass <- createTableClass columnClass moduScope
      -- !dbArrayClass <- createDbArrayClass columnClass defaultDataType moduScope

      {-
      !moduArts0 <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc moduScope mc nm hp
            | (mc, nm, hp) <-
                [
                  ( EdhMethod,

                    "arange",
                    wrapHostProc $ arangeProc defaultRangeDataType columnClass
                  ),
                  ( EdhMethod,
                    "random",
                    wrapHostProc $ randomProc defaultDataType columnClass
                  ),
                  (EdhMethod, "where", wrapHostProc whereProc),
                  ( EdhMethod,
                    "pi",
                    wrapHostProc $ piProc defaultDataType columnClass
                  ),
                  (EdhMethod, "exp", wrapHostProc $ floatOpProc float'exp),
                  (EdhMethod, "log", wrapHostProc $ floatOpProc float'log),
                  (EdhMethod, "sqrt", wrapHostProc $ floatOpProc float'sqrt),
                  (EdhMethod, "sin", wrapHostProc $ floatOpProc float'sin),
                  (EdhMethod, "cos", wrapHostProc $ floatOpProc float'cos),
                  (EdhMethod, "tan", wrapHostProc $ floatOpProc float'tan),
                  (EdhMethod, "asin", wrapHostProc $ floatOpProc float'asin),
                  (EdhMethod, "acos", wrapHostProc $ floatOpProc float'acos),
                  (EdhMethod, "atan", wrapHostProc $ floatOpProc float'atan),
                  (EdhMethod, "sinh", wrapHostProc $ floatOpProc float'sinh),
                  (EdhMethod, "cosh", wrapHostProc $ floatOpProc float'cosh),
                  (EdhMethod, "tanh", wrapHostProc $ floatOpProc float'tanh),
                  (EdhMethod, "asinh", wrapHostProc $ floatOpProc float'asinh),
                  (EdhMethod, "acosh", wrapHostProc $ floatOpProc float'acosh),
                  (EdhMethod, "atanh", wrapHostProc $ floatOpProc float'atanh)
                ]
          ]
                  -}

      let !moduArts =
            -- moduArts0 ++
            [ (AttrByName "Column", EdhObject columnClass)
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

withDtypeClass :: (Object -> EdhTx) -> EdhTx
withDtypeClass !act = importEdhModule "dim/dtypes" $ \ !moduDtypes !ets ->
  lookupEdhObjAttr moduDtypes (AttrByName "dtype") >>= \case
    (_, EdhObject !clsDtype) -> runEdhTx ets $ act clsDtype
    _ -> error "bug: dim/dtypes provides no dtype class"
