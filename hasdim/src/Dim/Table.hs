
module Dim.Table where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Foreign

import           Control.Monad
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


-- | A column is a 1-dimensional array with pre-allocated storage capacity,
-- safely typed for data manipulation.
data Column where
  Column ::(Storable a, EdhXchg a) => {
      -- convey type safe manipulation operations by an instance, making
      -- each column suitable to be wrapped within an untyped Edh object
      column'data'type :: !(DataType a)
      -- column length is number of valid elements, always smaller or equals
      -- to storage vector's length
    , column'length :: !(TVar Int)
      -- mark it obvious that the underlying storage is mutable anytime
      -- length of the Vector should be considered capacity of the column
    , column'storage :: !(TVar (IOVector a))
    } -> Column
 deriving Typeable

createColumn
  :: (Storable a, EdhXchg a)
  => EdhProgState
  -> DataType a
  -> EdhValue
  -> Int
  -> TVar Int
  -> (Column -> STM ())
  -> STM ()
createColumn !pgs !dt !iv !cap !lv !exit = create'data'vector dt pgs iv cap
  $ \ !cs -> join $ exit . Column dt lv <$> newTVar cs

columnLength :: Column -> STM Int
columnLength (Column _ !clv _) = readTVar clv

readColumnCell
  :: EdhProgState -> Int -> Column -> (EdhValue -> STM ()) -> STM ()
readColumnCell !pgs !idx (Column !dt _ !csv) !exit =
  readTVar csv >>= \ !cs -> read'data'vector'cell dt pgs idx cs exit

writeColumnCell :: EdhProgState -> EdhValue -> Int -> Column -> STM () -> STM ()
writeColumnCell !pgs !val !idx (Column !dt _ !csv) !exit =
  readTVar csv >>= \ !cs -> write'data'vector'cell dt pgs val idx cs exit

growColumn :: EdhProgState -> Column -> EdhValue -> Int -> STM () -> STM ()
growColumn !pgs (Column !dt _ !csv) !iv !cap !exit = readTVar csv >>= \ !cs ->
  grow'data'vector dt pgs cs iv cap $ \ !cs' -> writeTVar csv cs' >> exit


-- obtain valid column data as an immutable Storable Vector
--
-- this is as unsafe as unsafeFreeze is, pursuing zero-copy performance by
-- sacrificing thread safety
--
-- taking advantage of ForeignPtr under the hood in implementation details,
-- this avoids going through the IO Monad as to convert IOVector to Vector
-- by Data.Vector.Storable.Mutable api
columnData :: forall a . (Storable a, EdhXchg a) => Column -> STM (Vector a)
columnData (Column _ !clv !csv) = do
  !cl <- readTVar clv
  !cs <- readTVar csv
  case MV.unsafeToForeignPtr0 cs of
    (!p, _) -> return $ V.unsafeFromForeignPtr0 (castForeignPtr p) cl


