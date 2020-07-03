
module Dim.DataType where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Foreign

import           Control.Concurrent.STM


-- import           Data.Text                      ( Text )
-- import qualified Data.Text                     as T
-- import qualified Data.HashMap.Strict           as Map
-- import           Data.Dynamic
-- import           Data.Hashable

import           Data.Typeable

import           Data.Vector.Storable          as V
import           Data.Vector.Storable.Mutable  as MV
-- import qualified Data.Vector.Storable.Internal as V

import           Language.Edh.EHI

import           Dim.XCHG


-- type safe data manipulation operations wrt to exchanging data with Edh
-- programs
data DataType a where
  DataType ::(Storable a, EdhXchg a) => {
      create'data'vector ::  EdhProgState
        -> EdhValue -> Int -> (IOVector a -> STM ()) -> STM ()
    , read'data'vector'cell :: EdhProgState
        -> Int -> IOVector a -> (EdhValue -> STM ()) -> STM ()
    , write'data'vector'cell :: EdhProgState
        -> EdhValue -> Int -> IOVector a -> STM () -> STM ()
    , grow'data'vector :: EdhProgState
        -> IOVector a -> EdhValue -> Int -> (IOVector a -> STM ()) -> STM ()
  }-> DataType a
 deriving Typeable
dataType :: forall a . (Storable a, EdhXchg a) => DataType a
dataType = DataType createVector readVectorCell writeVectorCell growVector
 where
  createVector !pgs !iv !cap !exit =
    fromEdh pgs iv $ \ !isv -> exit $ doThraw $ V.replicate cap isv
  readVectorCell !pgs !idx !vec !exit =
    edhPerformIO pgs (MV.unsafeWith vec $ \ !vPtr -> peekElemOff vPtr idx)
      $ \ !sv -> contEdhSTM $ toEdh pgs sv $ \ !val -> exit val
  writeVectorCell !pgs !val !idx !vec !exit = fromEdh pgs val $ \ !sv -> do
    unsafeIOToSTM $ MV.unsafeWith vec $ \ !vPtr -> pokeElemOff vPtr idx sv
    exit
  growVector !pgs !vec !iv !cap !exit = if cap <= MV.length vec
    then exit $ MV.unsafeSlice 0 cap vec
    else fromEdh pgs iv $ \ !isv -> do
      let !vec'  = doThraw $ V.replicate cap isv
          cpData = MV.unsafeWith vec $ \ !p ->
            MV.unsafeWith vec' $ \ !p' -> copyArray p' p $ MV.length vec
      edhPerformIO pgs cpData $ \_ -> contEdhSTM $ exit vec'
  -- taking advantage of ForeignPtr under the hood in implementation details,
  -- this avoids going through the IO Monad as to create IOVector by
  -- Data.Vector.Storable.Mutable api
  doThraw :: Vector a -> IOVector a
  doThraw !vec = case V.unsafeToForeignPtr0 vec of
    (!p, !n) -> MV.unsafeFromForeignPtr0 p n
