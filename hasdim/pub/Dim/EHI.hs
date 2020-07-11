
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
import           Dim.Table


installDimBatteries :: EdhWorld -> IO ()
installDimBatteries !world =

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

    !dmpkTmplObj <- do
      !em     <- createSideEntityManipulater True =<< dmpkMethods pgs
      !clsVal <- mkHostClass moduScope "dmpk" dmpkCtor em
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

    !moduArts0 <- sequence
      [ (nm, ) <$> mkHostProc moduScope mc nm hp args
      | (mc, nm, hp, args) <-
        [ ( EdhMethod
          , "resolveDataType"
          , resolveDataTypeProc dtTmplObj
          , PackReceiver [mandatoryArg "dti"]
          )
        , ( EdhMethod
          , "resolveDataComparator"
          , resolveDataComparatorProc dmpkTmplObj
          , PackReceiver [mandatoryArg "dti"]
          )
        , ( EdhMethod
          , "resolveDataOperator"
          , resolveDataOperatorProc dmpkTmplObj
          , PackReceiver [mandatoryArg "dti"]
          )
        , ( EdhMethod
          , "resolveNumDataType"
          , resolveNumDataTypeProc numdtTmplObj
          , PackReceiver [mandatoryArg "dti"]
          )
        , ( EdhMethod
          , "arange"
          , arangeProc colTmplObj
          , PackReceiver [mandatoryArg "rangeSpec"]
          )
        ]
      ]

    let !moduArts =
          moduArts0
            ++ [ ("dtt"   , EdhObject dtTmplObj)
               , ("dmpkt" , EdhObject dmpkTmplObj)
               , ("numdtt", EdhObject numdtTmplObj)
               , ("colt"  , EdhObject colTmplObj)
               , ("Column", clsColumnVal)
               ]
    !artsDict <- createEdhDict
      $ Map.fromList [ (EdhString k, v) | (k, v) <- moduArts ]
    updateEntityAttrs pgs (objEntity modu)
      $  [ (AttrByName k, v) | (k, v) <- moduArts ]
      ++ [(AttrByName "__exports__", artsDict)]

    exit

