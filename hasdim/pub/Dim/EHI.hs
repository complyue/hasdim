{-# LANGUAGE AllowAmbiguousTypes #-}

module Dim.EHI
  ( installDimBatteries
  , module Dim.XCHG
  , module Dim.DataType
  , module Dim.Table
  )
where

import           Prelude
-- import           Debug.Trace

import           Foreign                 hiding ( void )

import           Control.Concurrent.STM

import           Control.Monad.Reader

import           Data.Foldable
import           Data.Dynamic

import           Language.Edh.EHI

import           Dim.XCHG
import           Dim.DataType
import           Dim.Column
import           Dim.Table
import           Dim.Array


builtinDataTypes :: Object -> ([(DataTypeIdent, Object)] -> STM ()) -> STM ()
builtinDataTypes !dtTmplObj !exit =
  flip id []
    $ mkDtAlias @Double "float64" ["f8"]
    $ mkDtAlias @Float "float32" ["f4"]
    $ mkDtAlias @Int64 "int64" ["i8"]
    $ mkDtAlias @Int32 "int32" ["i4"]
    $ mkDtAlias @Int8 "int8" []
    $ mkDtAlias @Word8 "byte" []
    $ mkDtAlias @Int "intp" []
    $ mkDtAlias @VecBool "bool" []
    $ exit
 where
  mkDtAlias
    :: forall a
     . (EdhXchg a, Storable a, Typeable a)
    => DataTypeIdent
    -> [DataTypeIdent]
    -> ([(DataTypeIdent, Object)] -> STM ())
    -> [(DataTypeIdent, Object)]
    -> STM ()
  mkDtAlias !dti !alias !exit' !dts =
    cloneEdhObject
        dtTmplObj
        (\_ !cloneExit -> do
          let !dt = makeDataType @a dti
          cloneExit $ toDyn dt
        )
      $ \ !dto -> exit'
          $ foldl' (\ !dts' !n -> (n, dto) : dts') ((dti, dto) : dts) alias


installDimBatteries :: EdhWorld -> IO ()
installDimBatteries !world = do


  !moduDtypes <- installEdhModule world "dim/dtypes" $ \ !pgs !exit -> do

    let !moduScope = contextScope $ edh'context pgs
        !modu      = thisObject moduScope

    !dtTmplObj <- do
      !em     <- createSideEntityManipulater True =<< dtypeMethods pgs
      !clsVal <- mkHostClass moduScope "dtype" dtypeCtor em
      !cls    <- case clsVal of
        EdhClass !cls -> return cls
        _             -> error "bug: mkHostClass returned non-class"
      !ent <- createSideEntity em $ toDyn nil
      viewAsEdhObject ent cls []

    builtinDataTypes dtTmplObj $ \ !dtAlias -> do

      let !moduArts = [ (k, EdhObject dto) | (k, dto) <- dtAlias ]
      !artsDict <- EdhDict
        <$> createEdhDict [ (EdhString k, v) | (k, v) <- moduArts ]
      updateEntityAttrs pgs (objEntity modu)
        $  [ (AttrByName k, v) | (k, v) <- moduArts ]
        ++ [(AttrByName "__exports__", artsDict)]

      exit


  void $ installEdhModule world "dim/symbols" $ \ !pgs !exit -> do

    let !moduScope = contextScope $ edh'context pgs
        !modu      = thisObject moduScope

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
    updateEntityAttrs pgs (objEntity modu)
      $  [ (AttrByName k, v) | (k, v) <- moduArts ]
      ++ [(AttrByName "__exports__", artsDict)]

    exit


  void $ installEdhModule world "dim/RT" $ \ !pgs !exit -> do

    defaultDataType <- lookupEntityAttr pgs
                                        (objEntity moduDtypes)
                                        (AttrByName "float64")
    defaultRangeDataType <- lookupEntityAttr pgs
                                             (objEntity moduDtypes)
                                             (AttrByName "intp")

    let !moduScope = contextScope $ edh'context pgs
        !modu      = thisObject moduScope

    !dmrpTmplObj <- do
      !em     <- createSideEntityManipulater True =<< dmrpMethods pgs
      !clsVal <- mkHostClass moduScope "dmrp" dmrpCtor em
      !cls    <- case clsVal of
        EdhClass !cls -> return cls
        _             -> error "bug: mkHostClass returned non-class"
      !ent <- createSideEntity em $ toDyn nil
      viewAsEdhObject ent cls []

    !numdtTmplObj <- do
      !em     <- createSideEntityManipulater True =<< numdtMethods pgs
      !clsVal <- mkHostClass moduScope "numdt" numdtCtor em
      !cls    <- case clsVal of
        EdhClass !cls -> return cls
        _             -> error "bug: mkHostClass returned non-class"
      !ent <- createSideEntity em $ toDyn nil
      viewAsEdhObject ent cls []

    !emColumn     <- createSideEntityManipulater True =<< colMethods pgs
    !clsColumnVal <- mkHostClass moduScope
                                 "Column"
                                 (colCtor defaultDataType)
                                 emColumn
    !clsColumn <- case clsColumnVal of
      EdhClass !clsColumn -> return clsColumn
      _                   -> error "bug: mkHostClass returned non-class"
    !colTmplObj <- do
      !ent <- createSideEntity emColumn $ toDyn nil
      viewAsEdhObject ent clsColumn []

    !moduArts0 <-
      sequence
      $  [ (AttrBySym sym, ) <$> mkSymbolicHostProc moduScope mc sym hp args
         | (mc, sym, hp, args) <-
           [ ( EdhMethod
             , resolveDataComparatorEffId
             , resolveDataComparatorProc dmrpTmplObj
             , PackReceiver [mandatoryArg "dti"]
             )
           , ( EdhMethod
             , resolveDataOperatorEffId
             , resolveDataOperatorProc dmrpTmplObj
             , PackReceiver [mandatoryArg "dti"]
             )
           , ( EdhMethod
             , resolveNumDataTypeEffId
             , resolveNumDataTypeProc numdtTmplObj
             , PackReceiver [mandatoryArg "dti"]
             )
           ]
         ]
      ++ [ (AttrByName nm, ) <$> mkHostProc moduScope mc nm hp args
         | (mc, nm, hp, args) <-
           [ ( EdhMethod
             , "arange"
             , arangeProc defaultRangeDataType colTmplObj
             , PackReceiver [mandatoryArg "rangeSpec"]
             )
           , ( EdhMethod
             , "where"
             , whereProc
             , PackReceiver
               [ mandatoryArg "predict"
               , optionalArg "trueData"  (LitExpr NilLiteral)
               , optionalArg "falseData" (LitExpr NilLiteral)
               ]
             )
           ]
         ]
      ++ [ ((AttrByName nm, ) <$>)
           $ mkExtHostClass moduScope nm hc
           $ \ !classUniq ->
               createSideEntityManipulater True =<< mths classUniq pgs
         | (nm, hc, mths) <-
           [ ("Table"  , tabCtor                , tabMethods colTmplObj)
           , ("DbArray", aryCtor defaultDataType, aryMethods)
           ]
         ]

    let !moduArts =
          moduArts0
            ++ [ (AttrByName "dmrpt" , EdhObject dmrpTmplObj)
               , (AttrByName "numdtt", EdhObject numdtTmplObj)
               , (AttrByName "colt"  , EdhObject colTmplObj)
               , (AttrByName "Column", clsColumnVal)
               ]
    !artsDict <- EdhDict
      <$> createEdhDict [ (attrKeyValue k, v) | (k, v) <- moduArts ]
    updateEntityAttrs pgs (objEntity modu)
      $  [ (k, v) | (k, v) <- moduArts ]
      ++ [(AttrByName "__exports__", artsDict)]

    exit

