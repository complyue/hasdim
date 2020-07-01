
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


class Table t where
  countRows :: t -> IO Int
  type RefTables t
  type RowType t
  getRow :: RefTables t -> t -> Int -> IO (RowType t)


-- atomic data types
type InstrumentId = Text
type TradeTime = Int64
type TradeMinutes = Int32


-- encode a field definition with a vanilla type
newtype TradeBegin = TradeBegin TradeTime
newtype TradeDuration = TradeDuration TradeMinutes


-- encode a table structure definition with a closed type family
type family TradePeriod field where
  -- encode table fields with data instances, 
  -- stating a column's atomic data type
  TradePeriod TradeBegin = TradeTime
  TradePeriod TradeDuration = TradeMinutes

-- encode the storage of a table column with a vector of its atomic data type
newtype TradePeriod'Column field = TradePeriod'Column
  (Vector (TradePeriod field))

-- encode the storage of a table with a vanilla ADT
data TradePeriod'Table = TradePeriod'Table
  !InstrumentId
  !(TradePeriod'Column TradeBegin)
  !(TradePeriod'Column TradeDuration)

-- encode the row type of a table with a vanilla ADT
data TradePeriod'Row = TradePeriod'Row
  !(TradePeriod TradeBegin)
  !(TradePeriod TradeDuration)

instance Table TradePeriod'Table where
  countRows (TradePeriod'Table _ (TradePeriod'Column !colTradeBegin) (TradePeriod'Column !colTradeDuration))
    = do
      let cnt = V.length colTradeBegin
      unless (cnt == V.length colTradeDuration) $ throwIO $ TypeError
        "length mismatch across columns"
      return cnt
  type RefTables TradePeriod'Table = ()
  type RowType TradePeriod'Table = TradePeriod'Row
  getRow () tab@(TradePeriod'Table _ (TradePeriod'Column !colTradeBegin) (TradePeriod'Column !colTradeDuration)) !row
    = do
      rowCnt <- countRows tab
      unless (row >= 0 && row < rowCnt) $ throwIO $ TypeError
        "row index out of range"
      return $ TradePeriod'Row (unsafeIndex colTradeBegin row)
                               (unsafeIndex colTradeDuration row)

-- boilerplate code for enumeration of all rows from a table
enumRowsOfTradePeriod
  :: TradePeriod'Table -> (Int -> TradePeriod'Row -> IO ()) -> IO ()
enumRowsOfTradePeriod tab@(TradePeriod'Table _ (TradePeriod'Column !colTradeBegin) (TradePeriod'Column !colTradeDuration)) !process
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



-- the field referencing a row in TradePeriod table
newtype MinuBar'TradePeriod = MinuBar'TradePeriod Int

-- open time of a bar, since begin of the trade period
newtype MinuBarOpen = MinuBarOpen TradeMinutes

-- minute bar table structure
type family MinuBar field where
  MinuBar MinuBar'TradePeriod = Int
  MinuBar MinuBarOpen = TradeMinutes

-- column data type for minute bar table
newtype MinuBar'Column field = MinuBar'Column
  (Vector (MinuBar field))

-- data type of a minute bar table
data MinuBar'Table = MinuBar'Table
  !InstrumentId
  !TradeMinutes -- single bar span
  !(MinuBar'Column MinuBar'TradePeriod)
  !(MinuBar'Column MinuBarOpen)

-- data type of a minute bar table raw
data MinuBar'Row = MinuBar'Row
  !TradePeriod'Row
  !(MinuBar MinuBarOpen)

instance Table MinuBar'Table where
  countRows (MinuBar'Table _ _ (MinuBar'Column !col'MinuBar'TradePeriod) (MinuBar'Column !col'MinuBarOpen))
    = do
      let cnt = V.length col'MinuBar'TradePeriod
      unless (cnt == V.length col'MinuBarOpen) $ throwIO $ TypeError
        "length mismatch across columns"
      return cnt
  type RefTables MinuBar'Table = TradePeriod'Table
  type RowType MinuBar'Table = MinuBar'Row
  getRow !tabTradePeriod tab@(MinuBar'Table _ _ (MinuBar'Column !col'MinuBar'TradePeriod) (MinuBar'Column !col'MinuBarOpen)) !row
    = do
      rowCnt <- countRows tab
      unless (row >= 0 && row < rowCnt) $ throwIO $ TypeError
        "row index out of range"
      rowTradePeriod <- getRow ()
                               tabTradePeriod
                               (unsafeIndex col'MinuBar'TradePeriod row)
      return $ MinuBar'Row rowTradePeriod (unsafeIndex col'MinuBarOpen row)



type Price = Double

newtype OpenPrice = OpenPrice Price
newtype HighPrice = HighPrice Price
newtype LowPrice = LowPrice Price
newtype ClosePrice  =ClosePrice Price

type family MinuOHLC field where
  MinuOHLC OpenPrice = Price
  MinuOHLC HighPrice = Price
  MinuOHLC LowPrice = Price
  MinuOHLC ClosePrice = Price

newtype MinuOHLC'Column field = MinuOHLC'Column
  (Vector (MinuOHLC field))

data MinuOHLC'Table = MinuOHLC'Table
  !(MinuOHLC'Column OpenPrice)
  !(MinuOHLC'Column HighPrice)
  !(MinuOHLC'Column LowPrice)
  !(MinuOHLC'Column ClosePrice)

data MinuOHLC'Row = MinuOHLC'Row
  !MinuBar'Row
  !(MinuOHLC OpenPrice)
  !(MinuOHLC HighPrice)
  !(MinuOHLC LowPrice)
  !(MinuOHLC ClosePrice)

instance Table MinuOHLC'Table where
  countRows (MinuOHLC'Table (MinuOHLC'Column !col'OpenPrice) (MinuOHLC'Column !col'HighPrice) (MinuOHLC'Column !col'LowPrice) (MinuOHLC'Column !col'ClosePrice))
    = do
      let cnt = V.length col'OpenPrice
      unless (cnt == V.length col'HighPrice) $ throwIO $ TypeError
        "length mismatch across columns"
      unless (cnt == V.length col'LowPrice) $ throwIO $ TypeError
        "length mismatch across columns"
      unless (cnt == V.length col'ClosePrice) $ throwIO $ TypeError
        "length mismatch across columns"
      return cnt
  type RefTables MinuOHLC'Table = (TradePeriod'Table, MinuBar'Table)
  type RowType MinuOHLC'Table = MinuOHLC'Row
  getRow (!tabTradePeriod, !tabMinuBar) tab@(MinuOHLC'Table (MinuOHLC'Column !col'OpenPrice) (MinuOHLC'Column !col'HighPrice) (MinuOHLC'Column !col'LowPrice) (MinuOHLC'Column !col'ClosePrice)) !row
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

enumRowsOfMinuOHLC
  :: TradePeriod'Table
  -> MinuBar'Table
  -> MinuOHLC'Table
  -> (Int -> MinuOHLC'Row -> IO ())
  -> IO ()
enumRowsOfMinuOHLC !tabTradePeriod !tabMinuBar tab@(MinuOHLC'Table (MinuOHLC'Column !col'OpenPrice) (MinuOHLC'Column !col'HighPrice) (MinuOHLC'Column !col'LowPrice) (MinuOHLC'Column !col'ClosePrice)) !process
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

