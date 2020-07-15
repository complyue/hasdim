
module Dim.EHI
  ( installDimBatteries
  , module Dim.XCHG
  , module Dim.DataType
  , module Dim.Table
  )
where

import           Prelude
-- import           Debug.Trace

import           Control.Monad.Reader

import           Data.Dynamic

import qualified Data.HashMap.Strict           as Map

import           Language.Edh.EHI

import           Dim.XCHG
import           Dim.DataType
import           Dim.Column
import           Dim.Table


installDimBatteries :: EdhWorld -> IO ()
installDimBatteries !world = do


  void $ installEdhModule world "dim/symbols" $ \pgs exit -> do

    let !moduScope = contextScope $ edh'context pgs
        !modu      = thisObject moduScope

    let
      !moduArts =
        [ (symbolName resolveDataTypeEffId, EdhSymbol resolveDataTypeEffId)
        , ( symbolName resolveDataComparatorEffId
          , EdhSymbol resolveDataComparatorEffId
          )
        , ( symbolName resolveDataOperatorEffId
          , EdhSymbol resolveDataOperatorEffId
          )
        , ( symbolName resolveNumDataTypeEffId
          , EdhSymbol resolveNumDataTypeEffId
          )
        ]
    !artsDict <- createEdhDict
      $ Map.fromList [ (EdhString k, v) | (k, v) <- moduArts ]
    updateEntityAttrs pgs (objEntity modu)
      $  [ (AttrByName k, v) | (k, v) <- moduArts ]
      ++ [(AttrByName "__exports__", artsDict)]

    exit


  void $ installEdhModule world "dim/RT" $ \pgs exit -> do

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
    !clsColumnVal <- mkHostClass moduScope "Column" colCtor emColumn
    !clsColumn    <- case clsColumnVal of
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
             , resolveDataTypeEffId
             , resolveDataTypeProc dtTmplObj
             , PackReceiver [mandatoryArg "dti"]
             )
           , ( EdhMethod
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
             , arangeProc colTmplObj
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
           $   mkHostClass moduScope nm hc
           =<< createSideEntityManipulater True
           =<< mths pgs
         | (nm, hc, mths) <- [("Table", tabCtor, tabMethods)]
         ]

    let !moduArts =
          moduArts0
            ++ [ (AttrByName "dtt"   , EdhObject dtTmplObj)
               , (AttrByName "dmrpt" , EdhObject dmrpTmplObj)
               , (AttrByName "numdtt", EdhObject numdtTmplObj)
               , (AttrByName "colt"  , EdhObject colTmplObj)
               , (AttrByName "Column", clsColumnVal)
               ]
    !artsDict <- createEdhDict
      $ Map.fromList [ (attrKeyValue k, v) | (k, v) <- moduArts ]
    updateEntityAttrs pgs (objEntity modu)
      $  [ (k, v) | (k, v) <- moduArts ]
      ++ [(AttrByName "__exports__", artsDict)]

    exit

