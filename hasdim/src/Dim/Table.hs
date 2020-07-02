
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

import           Data.Vector.Storable          as V
import           Data.Vector.Storable.Mutable  as MV
-- import qualified Data.Vector.Storable.Internal as V

import           Language.Edh.EHI

import           Dim.XCHG


data Column a where
  Column ::(Storable a, EdhXchg a) => {
    -- length of the Vector should be considered capacity of the column
    column'storage :: !(IOVector a)
    -- column length is always smaller or equals storage vector's length
  , column'length :: !(TVar Int)
  } -> Column a


-- as unsafe as unsafeFreeze, and without needing IO 
columnData :: (Storable a, EdhXchg a) => Column a -> Vector a
columnData (Column !mv _) = case MV.unsafeToForeignPtr0 mv of
  (!p, !n) -> V.unsafeFromForeignPtr p 0 n


readColumnAt
  :: (Storable a, EdhXchg a)
  => EdhProgState
  -> Int
  -> Column a
  -> (EdhValue -> STM ())
  -> STM ()
readColumnAt !pgs !idx (Column !vec _) !exit =
  edhPerformIO pgs (MV.unsafeWith vec $ \ !vPtr -> peekElemOff vPtr idx)
    $ \ !sv -> contEdhSTM $ toEdh pgs sv $ \ !val -> exit val

writeColumnAt
  :: (Storable a, EdhXchg a)
  => EdhProgState
  -> EdhValue
  -> Int
  -> Column a
  -> STM ()
  -> STM ()
writeColumnAt !pgs !val !idx (Column !vec _) !exit =
  fromEdh pgs val $ \ !sv -> do
    unsafeIOToSTM $ MV.unsafeWith vec $ \ !vPtr -> pokeElemOff vPtr idx sv
    exit


