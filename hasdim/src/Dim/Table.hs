
module Dim.Table where

import           Prelude
-- import           Debug.Trace

import           Unsafe.Coerce
import           GHC.Conc                       ( unsafeIOToSTM )

import           Foreign                 hiding ( void )

import           Control.Monad
import           Control.Monad.Reader

import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.HashMap.Strict           as Map

import           Data.Coerce
import           Data.Dynamic

import           Data.Vector                    ( Vector )

import           Data.Lossless.Decimal         as D

import           Language.Edh.EHI

import           Dim.XCHG
import           Dim.DataType
import           Dim.Column


data Table = Table {
    -- this is also the mutex to coordinate concurrent modifications to the
    -- table
    table'row'count :: !(TMVar Int)
    -- optional labels associated with each row
  , table'row'labels :: !(Maybe EdhVector)
    -- underlying table storage, represented as columns, those sharing 
  , table'columns :: !(Vector Column)
    -- labels associated with each column, default to their respective index
  , table'column'labels :: !EdhVector
  } deriving (Typeable)

