{-# LANGUAGE AllowAmbiguousTypes #-}

module Dim.EHI
  ( installDimBatteries,
    module Dim.XCHG,
    module Dim.DataType,
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
import Dim.DataType
import Dim.DbArray
import Dim.DbArts
import Dim.Float
import Dim.Table
import Dim.XCHG
import Foreign hiding (void)
import Language.Edh.EHI
import Prelude

builtinDataTypes :: Object -> STM [(DataTypeIdent, Object)]
builtinDataTypes !dtClass =
  concat
    <$> sequence
      [ mkDevTypeWithAlias @Double "float64" ["f8"],
        mkDevTypeWithAlias @Float "float32" ["f4"],
        mkDevTypeWithAlias @Int64 "int64" ["i8"],
        mkDevTypeWithAlias @Int32 "int32" ["i4"],
        mkDevTypeWithAlias @Int8 "int8" ["byte"],
        mkDevTypeWithAlias @Int "intp" [],
        mkDevTypeWithAlias @YesNo "yesno" ["bool"],
        mkHostTypeWithAlias @D.Decimal "decimal" D.nan [],
        mkHostTypeWithAlias @EdhValue
          "box"
          edhNA
          [ "object" -- for numpy compat, not all values are objects in Edh
          ]
      ]
  where
    mkDevTypeWithAlias ::
      forall a.
      (EdhXchg a, Typeable a, Storable a) =>
      DataTypeIdent ->
      [DataTypeIdent] ->
      STM [(DataTypeIdent, Object)]
    mkDevTypeWithAlias !dti !alias =
      let !dt = makeDeviceDataType @a dti
       in edhCreateHostObj dtClass (toDyn dt) []
            >>= \ !dto -> return $ ((dti, dto) :) $ (,dto) <$> alias

    mkHostTypeWithAlias ::
      forall a.
      (EdhXchg a, Typeable a) =>
      DataTypeIdent ->
      a ->
      [DataTypeIdent] ->
      STM [(DataTypeIdent, Object)]
    mkHostTypeWithAlias !dti !def'val !alias =
      let !dt = makeHostDataType @a dti def'val
       in edhCreateHostObj dtClass (toDyn dt) []
            >>= \ !dto -> return $ ((dti, dto) :) $ (,dto) <$> alias

installDimBatteries :: EdhWorld -> IO ()
installDimBatteries !world = do
  !moduDtypes <- installEdhModule world "dim/dtypes" $ \ !ets !exit -> do
    let !moduScope = contextScope $ edh'context ets

    !dtClass <- createDataTypeClass moduScope
    !dtAlias <- builtinDataTypes dtClass

    let !moduArts =
          ("dtype", EdhObject dtClass) :
            [(k, EdhObject dto) | (k, dto) <- dtAlias]
    !artsDict <-
      EdhDict <$> createEdhDict [(EdhString k, v) | (k, v) <- moduArts]
    flip iopdUpdate (edh'scope'entity moduScope) $
      [(AttrByName k, v) | (k, v) <- moduArts]
        ++ [(AttrByName "__exports__", artsDict)]

    exit

  void $
    installEdhModule world "dim/dtypes/effects" $ \ !ets !exit -> do
      let !moduScope = contextScope $ edh'context ets

      !moduArts <-
        sequence $
          [ (AttrByName $ "__DataComparator_" <> dti <> "__",)
              <$> fmap EdhObject (edhWrapHostValue ets hv)
            | (dti, hv) <-
                [ ("float64", deviceDataOrdering @Double),
                  ("float32", deviceDataOrdering @Float),
                  ("int64", deviceDataOrdering @Int64),
                  ("int32", deviceDataOrdering @Int32),
                  ("int8", deviceDataOrdering @Int8),
                  ("byte", deviceDataOrdering @Int8),
                  ("intp", deviceDataOrdering @Int),
                  ("yesno", deviceDataOrdering @YesNo),
                  ("decimal", hostDataOrdering @D.Decimal),
                  ("box", edhDataOrdering)
                ]
          ]
            ++ [ (AttrByName $ "__DataOperator_" <> dti <> "__",)
                   <$> fmap EdhObject (edhWrapHostValue ets hv)
                 | (dti, hv) <-
                     [ ("float64", deviceDataOperations @Double),
                       ("float32", deviceDataOperations @Float),
                       ("int64", deviceDataOperations @Int64),
                       ("int32", deviceDataOperations @Int32),
                       ("int8", deviceDataOperations @Int8),
                       ("byte", deviceDataOperations @Int8),
                       ("intp", deviceDataOperations @Int),
                       ("yesno", deviceDataOperations @YesNo),
                       ("decimal", hostDataOperations @D.Decimal D.nan),
                       ("box", edhDataOperations edhNA)
                     ]
               ]
            ++ [ (AttrByName $ "__NumDataType_" <> dti <> "__",)
                   <$> fmap EdhObject (edhWrapHostValue ets hv)
                 | (dti, hv) <-
                     [ ("float64", deviceDataNumbering @Double),
                       ("float32", deviceDataNumbering @Float),
                       ("int64", deviceDataNumbering @Int64),
                       ("int32", deviceDataNumbering @Int32),
                       ("int8", deviceDataNumbering @Int8),
                       ("byte", deviceDataNumbering @Int8),
                       ("intp", deviceDataNumbering @Int),
                       ("decimal", hostDataNumbering @D.Decimal D.nan),
                       ("box", edhDataNumbering)
                     ]
               ]
            ++ [ (AttrByName $ "__FloatDataOperator_" <> dti <> "__",)
                   <$> fmap EdhObject (edhWrapHostValue ets hv)
                 | (dti, hv) <-
                     [ ("float64", floatOperations @Double),
                       ("float32", floatOperations @Float)
                     ]
               ]

      !artsDict <-
        EdhDict
          <$> createEdhDict [(attrKeyValue k, v) | (k, v) <- moduArts]
      flip iopdUpdate (edh'scope'entity moduScope) $
        [(k, v) | (k, v) <- moduArts]
          ++ [(AttrByName "__exports__", artsDict)]

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
      !defaultRangeDataType <-
        fromJust <$> iopdLookup (AttrByName "intp") dtypesModuStore >>= \case
          EdhObject !dto -> return dto
          _ -> error "bug: dtype not object"

      let !moduScope = contextScope $ edh'context ets

      !columnClass <- createColumnClass defaultDataType moduScope
      !tableClass <- createTableClass columnClass moduScope
      !dbArrayClass <- createDbArrayClass columnClass defaultDataType moduScope

      !moduArts0 <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc moduScope mc nm hp
            | (mc, nm, hp) <-
                [ ( EdhMethod,
                    "arange",
                    wrapHostProc $ arangeProc defaultRangeDataType columnClass
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

      let !moduArts =
            moduArts0
              ++ [ (AttrByName "Column", EdhObject columnClass),
                   (AttrByName "Table", EdhObject tableClass),
                   (AttrByName "DbArray", EdhObject dbArrayClass)
                 ]

      !artsDict <-
        EdhDict
          <$> createEdhDict [(attrKeyValue k, v) | (k, v) <- moduArts]
      flip iopdUpdate (edh'scope'entity moduScope) $
        [(k, v) | (k, v) <- moduArts]
          ++ [(AttrByName "__exports__", artsDict)]

      exit
