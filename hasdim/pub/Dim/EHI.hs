
module Dim.EHI
  ( installDimBatteries
  , module Dim.XCHG
  , module Dim.Array
  )
where

import           Prelude
-- import           Debug.Trace

import           Control.Monad.Reader

import qualified Data.HashMap.Strict           as Map

import           Dim.Array

import           Language.Edh.EHI

import           Dim.XCHG


installDimBatteries :: EdhWorld -> IO ()
installDimBatteries !world =

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

