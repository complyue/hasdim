
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


-- general interface for data tables

class Table t where
  type RefTables t
  type RowType t

  countRows :: t -> IO Int

  getRow :: RefTables t -> t -> Int -> IO (RowType t)

  enumRows :: RefTables t -> t -> (Int -> RowType t-> IO ()) -> IO ()
  enumRows !refs !tab !process = do
    rowCnt <- countRows  tab
    let   go :: Int -> IO ()
          go !rowNo = if rowNo >= rowCnt
            then return ()
            else do
              row <- getRow refs tab rowNo
              process rowNo row
              go (rowNo + 1)
    go 0

-- tag for a data field type, mapping field definition type to respective
-- storage data type
-- the result types should normally each have a Storable instance
type family Field field

-- encode the storage data type of a table column as a Vector of its
-- respective field's Storable data type
newtype Column field = Column (Vector (Field field))



-- atomic storage data types

type InstrumentId = Text
type TradeTime = Int64
type TradeMinutes = Int32
type Price = Double


-- encode field definitions as vanilla ADTs with Field instance

newtype TradeBegin = TradeBegin TradeTime
type instance Field TradeBegin = TradeTime

newtype TradeDuration = TradeDuration TradeMinutes
type instance Field TradeDuration = TradeMinutes

-- the field referencing a row in TradePeriod table
newtype MinuBar'TradePeriod = MinuBar'TradePeriod Int
type instance Field MinuBar'TradePeriod = Int

-- open time of a bar, since begin of the trade period
newtype MinuBarOpen = MinuBarOpen TradeMinutes
type instance Field MinuBarOpen = TradeMinutes

newtype OpenPrice = OpenPrice Price
type instance Field OpenPrice = Price
newtype HighPrice = HighPrice Price
type instance Field HighPrice = Price
newtype LowPrice = LowPrice Price
type instance Field LowPrice = Price
newtype ClosePrice = ClosePrice Price
type instance Field ClosePrice = Price



-- encode the storage data type of a table as a vanilla ADT
data TradePeriod'Table = TradePeriod'Table
  !InstrumentId
  !(Column TradeBegin)
  !(Column TradeDuration)

-- encode the row type of a table as a vanilla ADT
data TradePeriod'Row = TradePeriod'Row
  !(Field TradeBegin)
  !(Field TradeDuration)

-- implement the Table class
instance Table TradePeriod'Table where
  type RefTables TradePeriod'Table = ()
  type RowType TradePeriod'Table = TradePeriod'Row

  countRows (TradePeriod'Table _ (Column !colTradeBegin) (Column !colTradeDuration))
    = do
      let cnt = V.length colTradeBegin
      unless (cnt == V.length colTradeDuration) $ throwIO $ TypeError
        "length mismatch across columns"
      return cnt
  getRow () tab@(TradePeriod'Table _ (Column !colTradeBegin) (Column !colTradeDuration)) !row
    = do
      rowCnt <- countRows tab
      unless (row >= 0 && row < rowCnt) $ throwIO $ TypeError
        "row index out of range"
      return $ TradePeriod'Row (unsafeIndex colTradeBegin row)
                               (unsafeIndex colTradeDuration row)
  -- boilerplate code to enumerate all rows from a table, eliding
  -- bounds checks for better performance
  enumRows () tab@(TradePeriod'Table _ (Column !colTradeBegin) (Column !colTradeDuration)) !process
    = do
      rowCnt <- countRows tab
      let go :: Int -> IO ()
          go !row = if row >= rowCnt
            then return ()
            else do
              process row $ TradePeriod'Row (unsafeIndex colTradeBegin row)
                                            (unsafeIndex colTradeDuration row)
              go $ row + 1
      go 0



-- storage data type of minute bar table
data MinuBar'Table = MinuBar'Table
  !InstrumentId
  !TradeMinutes -- single bar span
  !(Column MinuBar'TradePeriod)
  !(Column MinuBarOpen)

-- row type of minute bar table
data MinuBar'Row = MinuBar'Row
  !TradePeriod'Row
  !(Field MinuBarOpen)

-- implement the Table class
instance Table MinuBar'Table where
  type RefTables MinuBar'Table = TradePeriod'Table
  type RowType MinuBar'Table = MinuBar'Row

  countRows (MinuBar'Table _ _ (Column !col'MinuBar'TradePeriod) (Column !col'MinuBarOpen))
    = do
      let cnt = V.length col'MinuBar'TradePeriod
      unless (cnt == V.length col'MinuBarOpen) $ throwIO $ TypeError
        "length mismatch across columns"
      return cnt
  getRow !tabTradePeriod tab@(MinuBar'Table _ _ (Column !col'MinuBar'TradePeriod) (Column !col'MinuBarOpen)) !row
    = do
      rowCnt <- countRows tab
      unless (row >= 0 && row < rowCnt) $ throwIO $ TypeError
        "row index out of range"
      rowTradePeriod <- getRow ()
                               tabTradePeriod
                               (unsafeIndex col'MinuBar'TradePeriod row)
      return $ MinuBar'Row rowTradePeriod (unsafeIndex col'MinuBarOpen row)



-- the storage data type of minute ohlc bar table
data MinuOHLC'Table = MinuOHLC'Table
  !(Column OpenPrice)
  !(Column HighPrice)
  !(Column LowPrice)
  !(Column ClosePrice)

-- row type of minute ohlc bar table
data MinuOHLC'Row = MinuOHLC'Row
  !MinuBar'Row
  !(Field OpenPrice)
  !(Field HighPrice)
  !(Field LowPrice)
  !(Field ClosePrice)

-- implement the Table class
instance Table MinuOHLC'Table where
  type RefTables MinuOHLC'Table = (TradePeriod'Table, MinuBar'Table)
  type RowType MinuOHLC'Table = MinuOHLC'Row

  countRows (MinuOHLC'Table (Column !col'OpenPrice) (Column !col'HighPrice) (Column !col'LowPrice) (Column !col'ClosePrice))
    = do
      let cnt = V.length col'OpenPrice
      unless (cnt == V.length col'HighPrice) $ throwIO $ TypeError
        "length mismatch across columns"
      unless (cnt == V.length col'LowPrice) $ throwIO $ TypeError
        "length mismatch across columns"
      unless (cnt == V.length col'ClosePrice) $ throwIO $ TypeError
        "length mismatch across columns"
      return cnt
  getRow (!tabTradePeriod, !tabMinuBar) tab@(MinuOHLC'Table (Column !col'OpenPrice) (Column !col'HighPrice) (Column !col'LowPrice) (Column !col'ClosePrice)) !row
    = do
      rowCnt0 <- countRows tabMinuBar
      rowCnt  <- countRows tab
      unless (rowCnt == rowCnt0) $ throwIO $ TypeError
        "row count mismatch across tables"
      unless (row >= 0 && row < rowCnt) $ throwIO $ TypeError
        "row index out of range"
      rowTradePeriod <- getRow tabTradePeriod tabMinuBar row
      return $ MinuOHLC'Row rowTradePeriod
                            (unsafeIndex col'OpenPrice row)
                            (unsafeIndex col'HighPrice row)
                            (unsafeIndex col'LowPrice row)
                            (unsafeIndex col'ClosePrice row)
  enumRows (!tabTradePeriod, !tabMinuBar) tab@(MinuOHLC'Table (Column !col'OpenPrice) (Column !col'HighPrice) (Column !col'LowPrice) (Column !col'ClosePrice)) !process
    = do
      rowCnt <- countRows tab
      let go :: Int -> IO ()
          go !row = if row >= rowCnt
            then return ()
            else do
              rowTradePeriod <- getRow tabTradePeriod tabMinuBar row
              process row $ MinuOHLC'Row rowTradePeriod
                                         (unsafeIndex col'OpenPrice row)
                                         (unsafeIndex col'HighPrice row)
                                         (unsafeIndex col'LowPrice row)
                                         (unsafeIndex col'ClosePrice row)
              go $ row + 1
      go 0

