
module Dim.EHI
  ( installDimBatteries
  , module Dim.XCHG
  , module Dim.DataType
  , module Dim.Table
  )
where

import           Prelude
-- import           Debug.Trace

import           Control.Exception

import           Control.Concurrent.STM

import           Control.Monad.Reader

import           Data.Int
import           Data.Word

import qualified Data.HashMap.Strict           as Map

import           Language.Edh.EHI

import           Dim.XCHG
import           Dim.DataType
import           Dim.Table


installDimBatteries :: EdhWorld -> IO ()
installDimBatteries !world = do

  moduDtypes <- installEdhModule world "dim/dtypes" $ \pgs exit -> do

    let moduScope = contextScope $ edh'context pgs
        modu      = thisObject moduScope

    dtypeClassVal <-
      mkHostClass moduScope "dtype" dtypeCtor
      =<< createSideEntityManipulater True
      =<< dtypeMethods pgs
    let !dtypeClass = case dtypeClassVal of
          EdhClass !cls -> cls
          _             -> error "bug: mkHostClass returned non-class"
        !f8   = dataType "float64" :: DataType Double
        !f4   = dataType "float32" :: DataType Float
        !i8   = dataType "int64" :: DataType Int64
        !i4   = dataType "int32" :: DataType Int32
        !int8 = dataType "int8" :: DataType Int8
        !byte = dataType "byte" :: DataType Word8
        !intp = dataType "intp" :: DataType Int
        !bool = dataType "bool" :: DataType VecBool
        !dtypes =
          [ (ConcreteDataType f8  , ["f8"])
          , (ConcreteDataType f4  , ["f4"])
          , (ConcreteDataType i8  , ["i8"])
          , (ConcreteDataType i4  , ["i4"])
          , (ConcreteDataType int8, [])
          , (ConcreteDataType byte, [])
          , (ConcreteDataType intp, [])
          , (ConcreteDataType bool, [])
          ]

    seqcontSTM (wrapDataType pgs dtypeClass <$> dtypes) $ \ !dts -> do

      artsDict <-
        createEdhDict
        $  Map.fromList
        $  [ (EdhString k, v) | (names, v) <- dts, k <- names ]
        ++ [(EdhString "dtype", dtypeClassVal)]
      updateEntityAttrs pgs (objEntity modu)
        $  [ (AttrByName k, v) | (names, v) <- dts, k <- names ]
        ++ [(AttrByName "dtype", dtypeClassVal)]
        ++ [(AttrByName "__exports__", artsDict)]

      exit

  void $ installEdhModule world "dim/RT" $ \pgs exit -> do

    let !moduScope = contextScope $ edh'context pgs
        !modu      = thisObject moduScope

    !defaultDataType <- lookupEntityAttr pgs
                                         (objEntity moduDtypes)
                                         (AttrByName "f8")
    !indexDTO <-
      lookupEntityAttr pgs (objEntity moduDtypes) (AttrByName "intp") >>= \case
        EdhObject !dto -> return dto
        _              -> throwSTM $ TypeError "bug: bad DataType object intp"
    !boolDTO <-
      lookupEntityAttr pgs (objEntity moduDtypes) (AttrByName "bool") >>= \case
        EdhObject !dto -> return dto
        _              -> throwSTM $ TypeError "bug: bad DataType object bool"

    !emColumn <-
      createSideEntityManipulater True =<< colMethods indexDTO boolDTO pgs
    !clsColumnVal <- mkHostClass moduScope
                                 "Column"
                                 (colCtor defaultDataType)
                                 emColumn
    !clsColumn <- case clsColumnVal of
      EdhClass !clsColumn -> return clsColumn
      _                   -> error "bug: mkHostClass returned non-class"

    !moduArts0 <-
      sequence
      $  [ ((nm, ) <$>)
           $   mkHostClass moduScope nm hc
           =<< createSideEntityManipulater True
           =<< mths pgs
        --("Column", colCtor defaultDataType, colMethods indexDTO boolDTO)
         | (nm, hc, mths) <- []
         ]
      ++ [ (nm, ) <$> mkHostProc moduScope mc nm hp args
         | (mc, nm, hp, args) <-
           [ ( EdhMethod
             , "arange"
             , arangeProc indexDTO emColumn clsColumn
             , PackReceiver [mandatoryArg "rangeSpec"]
             )
           ]
         ]

    let !moduArts = moduArts0 ++ [("Column", clsColumnVal)]
    !artsDict <- createEdhDict
      $ Map.fromList [ (EdhString k, v) | (k, v) <- moduArts ]
    updateEntityAttrs pgs (objEntity modu)
      $  [ (AttrByName k, v) | (k, v) <- moduArts ]
      ++ [(AttrByName "__exports__", artsDict)]

    exit

