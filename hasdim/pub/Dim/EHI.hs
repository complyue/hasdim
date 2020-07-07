
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
        !f8   = dataType :: DataType Double
        !f4   = dataType :: DataType Float
        !i8   = dataType :: DataType Int64
        !i4   = dataType :: DataType Int32
        !int8 = dataType :: DataType Int8
        !byte = dataType :: DataType Word8
        !intp = dataType :: DataType Int
        !bool = dataType :: DataType Int8
        !char = dataType :: DataType Char
        !dtypes =
          [ (ConcreteDataType "float64" f8, ["f8"])
          , (ConcreteDataType "float32" f4, ["f4"])
          , (ConcreteDataType "int64" i8  , ["i8"])
          , (ConcreteDataType "int32" i4  , ["i4"])
          , (ConcreteDataType "int8" int8 , [])
          , (ConcreteDataType "byte" byte , [])
          , (ConcreteDataType "intp" intp , [])
          , (ConcreteDataType "bool" bool , [])
          , (ConcreteDataType "char" char , [])
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

    defaultDataType <- lookupEntityAttr pgs
                                        (objEntity moduDtypes)
                                        (AttrByName "f8")

    let moduScope = contextScope $ edh'context pgs
        modu      = thisObject moduScope

    !moduArts <- sequence
      [ ((nm, ) <$>)
        $   mkHostClass moduScope nm hc
        =<< createSideEntityManipulater True
        =<< mths pgs
      | (nm, hc, mths) <- [("Column", colCtor defaultDataType, colMethods)]
      ]

    artsDict <- createEdhDict
      $ Map.fromList [ (EdhString k, v) | (k, v) <- moduArts ]
    updateEntityAttrs pgs (objEntity modu)
      $  [ (AttrByName k, v) | (k, v) <- moduArts ]
      ++ [(AttrByName "__exports__", artsDict)]

    exit

