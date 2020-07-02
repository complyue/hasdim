
module Dim.Table where

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


data DataType a where
  DataType ::(Storable a, EdhXchg a) => {
      create'vector :: a -> Int -> (IOVector a -> STM ()) -> STM ()
    , read'vector'cell :: EdhProgState
        -> Int -> IOVector a -> (EdhValue -> STM ()) -> STM ()
    , write'vector'cell :: EdhProgState
        -> EdhValue -> Int -> IOVector a -> STM () -> STM ()
  }-> DataType a
 deriving Typeable
dataType :: forall a . (Storable a, EdhXchg a) => DataType a
dataType = DataType createVector readVectorCell writeVectorCell
 where
  doThraw :: Vector a -> IOVector a
  doThraw !vec = case V.unsafeToForeignPtr0 vec of
    (!p, !n) -> MV.unsafeFromForeignPtr0 p n
  createVector !iv !cap !exit = exit $ (doThraw $ V.replicate cap iv)
  readVectorCell !pgs !idx !vec !exit =
    edhPerformIO pgs (MV.unsafeWith vec $ \ !vPtr -> peekElemOff vPtr idx)
      $ \ !sv -> contEdhSTM $ toEdh pgs sv $ \ !val -> exit val
  writeVectorCell !pgs !val !idx !vec !exit = fromEdh pgs val $ \ !sv -> do
    unsafeIOToSTM $ MV.unsafeWith vec $ \ !vPtr -> pokeElemOff vPtr idx sv
    exit

data Column  where
  Column ::(Storable a, EdhXchg a) => {
      column'data'type :: !(DataType a)
      -- length of the Vector should be considered capacity of the column
    , column'storage :: !(IOVector a)
      -- column length is always smaller or equals storage vector's length
    , column'length :: !(TVar Int)
    } -> Column
 deriving Typeable

readColumnCell
  :: EdhProgState -> Int -> Column -> (EdhValue -> STM ()) -> STM ()
readColumnCell !pgs !idx (Column !dt !cs _) !exit =
  read'vector'cell dt pgs idx cs exit

writeColumnCell :: EdhProgState -> EdhValue -> Int -> Column -> STM () -> STM ()
writeColumnCell !pgs !val !idx (Column !dt !cs _) !exit =
  write'vector'cell dt pgs val idx cs exit


-- as unsafe as unsafeFreeze, but without needing IO 
columnData :: forall a . (Storable a, EdhXchg a) => Column -> Vector a
columnData (Column _ !mv _) = case MV.unsafeToForeignPtr0 mv of
  (!p, !n) -> V.unsafeFromForeignPtr0 (castForeignPtr p) n


