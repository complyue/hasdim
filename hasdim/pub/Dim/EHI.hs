
module Dim.EHI
  ( installDimBatteries
  , module Dim.XCHG
  , module Dim.Array
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
import           Dim.Array


installDimBatteries :: EdhWorld -> IO ()
installDimBatteries !world = do

  void $ installEdhModule world "dim/dtypes" $ \pgs exit -> do

    let moduScope = contextScope $ edh'context pgs
        modu      = thisObject moduScope

    dtypeClassVal <- mkHostClass moduScope "dtype" True dtypeCtor
    let !dtypeClass = case dtypeClassVal of
          EdhClass !cls -> cls
          _             -> error "bug: mkHostClass returned non-class"
        !f8 = dataType :: DataType Double
        !f4 = dataType :: DataType Float
        !i8 = dataType :: DataType Int64
        !i4 = dataType :: DataType Int32
        !w1 = dataType :: DataType Word8
        !u  = dataType :: DataType Char
        !dtypes =
          [ (ConcreteDataType "float64" f8, ["f8"])
          , (ConcreteDataType "float32" f4, ["f4"])
          , (ConcreteDataType "int64" i8  , ["i8"])
          , (ConcreteDataType "int32" i4  , ["i4"])
          , (ConcreteDataType "int8" w1   , ["byte", "w1"])
          , (ConcreteDataType "char" u    , ["w4"])
          ]

    seqcontSTM (wrapDataType pgs dtypeClass <$> dtypes) $ \ !dts -> do

      artsDict <- createEdhDict
        $ Map.fromList [ (EdhString k, v) | (names, v) <- dts, k <- names ]
      updateEntityAttrs pgs (objEntity modu)
        $  [ (AttrByName k, v) | (names, v) <- dts, k <- names ]
        ++ [(AttrByName "__exports__", artsDict)]

      exit


  void $ installEdhModule world "dim/Array" $ \pgs exit -> do

    let moduScope = contextScope $ edh'context pgs
        modu      = thisObject moduScope

    !moduArts <- sequence
      [ (nm, ) <$> mkHostClass moduScope nm True hc
      | (nm, hc) <- [("DimArray", aryHostCtor)]
      ]

    artsDict <- createEdhDict
      $ Map.fromList [ (EdhString k, v) | (k, v) <- moduArts ]
    updateEntityAttrs pgs (objEntity modu)
      $  [ (AttrByName k, v) | (k, v) <- moduArts ]
      ++ [(AttrByName "__exports__", artsDict)]

    exit

