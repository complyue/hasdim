
module Schema where

import           Prelude
-- import           Debug.Trace

import           Foreign

import           Control.Exception
import           Control.Monad.Reader


import           Data.Text                      ( Text )
-- import qualified Data.Text                     as T
-- import qualified Data.HashMap.Strict           as Map
-- import           Data.Dynamic
-- import           Data.Hashable

import           Data.Vector.Storable          as V

import           Dim.XCHG


-- general interface for data tables

class Table t where
  type RefTables t
  type RowType t

  countRows :: RefTables t -> t -> IO Int

  unsafeGetRow :: RefTables t -> t -> Int -> IO (RowType t)

  getRow :: RefTables t -> t -> Int -> IO (RowType t)
  getRow !refs !tab !rowNo = do
      rowCnt <- countRows refs tab
      unless (rowNo >= 0 && rowNo < rowCnt) $ throwIO $ TypeError
        "row index out of range"
      unsafeGetRow refs tab rowNo

  enumRows :: RefTables t -> t -> (Int -> RowType t-> IO ()) -> IO ()
  enumRows !refs !tab !process = do
    rowCnt <- countRows refs tab
    let   go :: Int -> IO ()
          go !rowNo = if rowNo >= rowCnt
            then return ()
            else do
              row <- unsafeGetRow refs tab rowNo
              process rowNo row
              go (rowNo + 1)
    go 0

-- tag for a data field type
type Field t = t
-- column storage type for a field
type Column t = (EdhXchg (Field t), Storable (Field t)) => Vector (Field t)



-- atomic storage data types

type InstrumentId = Text
type TradeTime = Int64
type TradeMinutes = Int32
type Price = Double



-- encode the storage data type of a table as a vanilla strict ADT
data TradePeriod'Table = TradePeriod'Table {
    meta'TradePeriod'InstruId :: !InstrumentId
  , pk'TradePeriod'Begin :: !(Column TradeTime)
  , col'TradePeriod'Duration :: !(Column TradeMinutes)
  }

-- encode the row type of a table as a vanilla lazy ADT
data TradePeriod'Row = TradePeriod'Row {
    row'TradePeriod'Begin :: (Field TradeTime)
  , row'TradePeriod'Duration :: (Field TradeMinutes)
  }

-- implement the Table class
instance Table TradePeriod'Table where
  type RefTables TradePeriod'Table = ()
  type RowType TradePeriod'Table = TradePeriod'Row

  countRows () (TradePeriod'Table _ (!colTradeBegin) (!colTradeDuration)) = do
    let cnt = V.length colTradeBegin
    unless (cnt == V.length colTradeDuration) $ throwIO $ TypeError
      "length mismatch across columns"
    return cnt
  unsafeGetRow () (TradePeriod'Table _ (!colTradeBegin) (!colTradeDuration)) !rowNo
    = return $ TradePeriod'Row (unsafeIndex colTradeBegin rowNo)
                               (unsafeIndex colTradeDuration rowNo)



-- storage data type of minute bar table
data MinuBar'Table = MinuBar'Table {
    meta'MinuBar'InstruId :: !InstrumentId
    -- single bar span
  , meta'MinuBar'Freq :: !TradeMinutes
    -- foreign key, referencing TradePeriod table
  , fk'MinuBar'TradePeriod :: !(Column Int)
    -- number of minutes elapsed since period begin
  , col'MinuBar'OpenTime :: !(Column TradeMinutes)
  }

-- row type of minute bar table
data MinuBar'Row = MinuBar'Row {
    ref'MinuBar'TradePeriod :: TradePeriod'Row
  , row'MinuBar'OpenTime :: (Field TradeMinutes)
  }

-- implement the Table class
instance Table MinuBar'Table where
  type RefTables MinuBar'Table = TradePeriod'Table
  type RowType MinuBar'Table = MinuBar'Row

  countRows _tabTradePeriod (MinuBar'Table _ _ (!col'MinuBar'TradePeriod) (!col'MinuBarOpen))
    = do
      let cnt = V.length col'MinuBar'TradePeriod
      unless (cnt == V.length col'MinuBarOpen) $ throwIO $ TypeError
        "length mismatch across columns"
      return cnt
  unsafeGetRow !tabTradePeriod (MinuBar'Table _ _ (!col'MinuBar'TradePeriod) (!col'MinuBarOpen)) !rowNo
    = do
      rowTradePeriod <- unsafeGetRow
        ()
        tabTradePeriod
        (unsafeIndex col'MinuBar'TradePeriod rowNo)
      return $ MinuBar'Row rowTradePeriod (unsafeIndex col'MinuBarOpen rowNo)



-- the storage data type of minute ohlc bar table
-- physically aligned with the MinuBar table having same instru & freq
data MinuOHLC'Table = MinuOHLC'Table {
    meta'MinuOHLC'InstruId
    -- single bar span
  , meta'MinuOHLC'Freq :: !TradeMinutes
    -- ohlc as 4 columns
  , col'MinuOHLC'OpenPrice :: !(Column Price)
  , col'MinuOHLC'HighPrice ::  !(Column Price)
  , col'MinuOHLC'LowPrice ::  !(Column Price)
  , col'MinuOHLC'ClosePrice ::  !(Column Price)
  }

-- row type of minute ohlc bar table
data MinuOHLC'Row = MinuOHLC'Row {
    ref'MinuOHLC'MinuBar :: MinuBar'Row
  , row'MinuOHLC'OpenPrice :: (Field Price)
  , row'MinuOHLC'HighPrice ::  (Field Price)
  , row'MinuOHLC'LowPrice ::  (Field Price)
  , row'MinuOHLC'ClosePrice ::  (Field Price)
  }

-- implement the Table class
instance Table MinuOHLC'Table where
  type RefTables MinuOHLC'Table = (TradePeriod'Table, MinuBar'Table)
  type RowType MinuOHLC'Table = MinuOHLC'Row

  countRows (!tabTradePeriod, !tabMinuBar) (MinuOHLC'Table _ _ (!col'OpenPrice) (!col'HighPrice) (!col'LowPrice) (!col'ClosePrice))
    = do
      cnt <- countRows tabTradePeriod tabMinuBar
      unless (cnt == V.length col'OpenPrice) $ throwIO $ TypeError
        "length mismatch across columns"
      unless (cnt == V.length col'HighPrice) $ throwIO $ TypeError
        "length mismatch across columns"
      unless (cnt == V.length col'LowPrice) $ throwIO $ TypeError
        "length mismatch across columns"
      unless (cnt == V.length col'ClosePrice) $ throwIO $ TypeError
        "length mismatch across columns"
      return cnt
  unsafeGetRow (!tabTradePeriod, !tabMinuBar) (MinuOHLC'Table _ _ (!col'OpenPrice) (!col'HighPrice) (!col'LowPrice) (!col'ClosePrice)) !rowNo
    = do
      rowMinuBar <- unsafeGetRow tabTradePeriod tabMinuBar rowNo
      return $ MinuOHLC'Row rowMinuBar
                            (unsafeIndex col'OpenPrice rowNo)
                            (unsafeIndex col'HighPrice rowNo)
                            (unsafeIndex col'LowPrice rowNo)
                            (unsafeIndex col'ClosePrice rowNo)


