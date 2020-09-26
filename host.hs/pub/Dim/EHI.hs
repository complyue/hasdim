{-# LANGUAGE AllowAmbiguousTypes #-}

module Dim.EHI
  ( installDimBatteries
  , module Dim.XCHG
  , module Dim.DataType
  , module Dim.Table
  , module Dim.DbArray
  )
where

import           Prelude
-- import           Debug.Trace

import           Foreign                 hiding ( void )

import           Control.Concurrent.STM

import           Control.Monad.Reader

import           Data.Maybe
import           Data.Dynamic

import           Language.Edh.EHI
import qualified Data.Lossless.Decimal         as D

import           Dim.XCHG
import           Dim.DataType
import           Dim.ColArts
import           Dim.Table
import           Dim.DbArray
import           Dim.DbArts


builtinDataTypes :: Object -> STM [(DataTypeIdent, Object)]
builtinDataTypes !dtClass = concat <$> sequence
  [ mkDevTypeWithAlias @Double "float64" ["f8"]
  , mkDevTypeWithAlias @Float "float32" ["f4"]
  , mkDevTypeWithAlias @Int64 "int64" ["i8"]
  , mkDevTypeWithAlias @Int32 "int32" ["i4"]
  , mkDevTypeWithAlias @Int8 "int8" ["byte"]
  , mkDevTypeWithAlias @Int "intp" []
  , mkDevTypeWithAlias @YesNo "yesno" ["bool"]
  , mkHostTypeWithAlias @D.Decimal "decimal" D.nan []
  , mkHostTypeWithAlias @EdhValue "box"
                                  edhNA
                                  [
                                   -- kinda for numpy compat,
                                   "object" -- not all values
                                   -- are objects in Edh
                                           ]
  ]
 where

  mkDevTypeWithAlias
    :: forall a
     . (EdhXchg a, Typeable a, Storable a)
    => DataTypeIdent
    -> [DataTypeIdent]
    -> STM [(DataTypeIdent, Object)]
  mkDevTypeWithAlias !dti !alias =
    let !dt = makeDeviceDataType @a dti
    in  edhCreateHostObj dtClass (toDyn dt) []
          >>= \ !dto -> return $ ((dti, dto) :) $ (, dto) <$> alias

  mkHostTypeWithAlias
    :: forall a
     . (EdhXchg a, Typeable a)
    => DataTypeIdent
    -> a
    -> [DataTypeIdent]
    -> STM [(DataTypeIdent, Object)]
  mkHostTypeWithAlias !dti !def'val !alias =
    let !dt = makeHostDataType @a dti def'val
    in  edhCreateHostObj dtClass (toDyn dt) []
          >>= \ !dto -> return $ ((dti, dto) :) $ (, dto) <$> alias


installDimBatteries :: EdhWorld -> IO ()
installDimBatteries !world = do


  void $ installEdhModule world "dim/symbols" $ \ !ets !exit -> do

    let !moduScope = contextScope $ edh'context ets

    let
      !moduArts =
        [ ( symbolName resolveDataComparatorEffId
          , EdhSymbol resolveDataComparatorEffId
          )
        , ( symbolName resolveDataOperatorEffId
          , EdhSymbol resolveDataOperatorEffId
          )
        , ( symbolName resolveNumDataTypeEffId
          , EdhSymbol resolveNumDataTypeEffId
          )
        ]
    !artsDict <- EdhDict
      <$> createEdhDict [ (EdhString k, v) | (k, v) <- moduArts ]
    flip iopdUpdate (edh'scope'entity moduScope)
      $  [ (AttrByName k, v) | (k, v) <- moduArts ]
      ++ [(AttrByName "__exports__", artsDict)]

    exit


  !moduDtypes <- installEdhModule world "dim/dtypes" $ \ !ets !exit -> do

    let !moduScope = contextScope $ edh'context ets

    !dtClass <- createDataTypeClass moduScope
    !dtAlias <- builtinDataTypes dtClass

    let !moduArts =
          ("dtype", EdhObject dtClass)
            : [ (k, EdhObject dto) | (k, dto) <- dtAlias ]
    !artsDict <- EdhDict
      <$> createEdhDict [ (EdhString k, v) | (k, v) <- moduArts ]
    flip iopdUpdate (edh'scope'entity moduScope)
      $  [ (AttrByName k, v) | (k, v) <- moduArts ]
      ++ [(AttrByName "__exports__", artsDict)]

    exit


  void $ installEdhModule world "dim/RT" $ \ !ets !exit -> do

    let !dtypesModuStore = case edh'obj'store moduDtypes of
          HashStore !hs -> hs
          _             -> error "bug: module not bearing hash store"

    !defaultDataType <-
      fromJust <$> iopdLookup (AttrByName "float64") dtypesModuStore >>= \case
        EdhObject !dto -> return dto
        _              -> error "bug: dtype not object"
    !defaultRangeDataType <-
      fromJust <$> iopdLookup (AttrByName "intp") dtypesModuStore >>= \case
        EdhObject !dto -> return dto
        _              -> error "bug: dtype not object"

    let !moduScope = contextScope $ edh'context ets

    !dbArrayClass <- createDbArrayClass defaultDataType moduScope
    !dmrpClass    <- createDMRPClass moduScope
    !numdtClass   <- createNumDataTypeClass moduScope
    !columnClass  <- createColumnClass defaultDataType moduScope
    !tableClass   <- createTableClass columnClass moduScope

    !moduArts0    <-
      sequence
      $  [ (AttrBySym sym, ) <$> mkSymbolicHostProc moduScope mc sym hp
         | (mc, sym, hp) <-
           [ ( EdhMethod
             , resolveDataComparatorEffId
             , wrapHostProc $ resolveDataComparatorProc dmrpClass
             )
           , ( EdhMethod
             , resolveDataOperatorEffId
             , wrapHostProc $ resolveDataOperatorProc dmrpClass
             )
           , ( EdhMethod
             , resolveNumDataTypeEffId
             , wrapHostProc $ resolveNumDataTypeProc numdtClass
             )
           ]
         ]
      ++ [ (AttrByName nm, ) <$> mkHostProc moduScope mc nm hp
         | (mc, nm, hp) <-
           [ ( EdhMethod
             , "arange"
             , wrapHostProc $ arangeProc defaultRangeDataType columnClass
             )
           , (EdhMethod, "where", wrapHostProc whereProc)
           ]
         ]

    let !moduArts =
          moduArts0
            ++ [ (AttrByName "DbArray", EdhObject dbArrayClass)
               , (AttrByName "Column" , EdhObject columnClass)
               , (AttrByName "Table"  , EdhObject tableClass)
               ]

    !artsDict <- EdhDict
      <$> createEdhDict [ (attrKeyValue k, v) | (k, v) <- moduArts ]
    flip iopdUpdate (edh'scope'entity moduScope)
      $  [ (k, v) | (k, v) <- moduArts ]
      ++ [(AttrByName "__exports__", artsDict)]

    exit

