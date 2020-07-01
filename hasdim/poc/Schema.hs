
module Schema where

import           Prelude
-- import           Debug.Trace

import           Foreign

import           Control.Exception
import           Control.Monad.Reader

-- import           Data.Text                      ( Text )
-- import qualified Data.Text                     as T
-- import qualified Data.HashMap.Strict           as Map
-- import           Data.Dynamic
-- import           Data.Hashable

import           Data.Vector.Storable          as V


-- atomic data types
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
  !(TradePeriod'Column TradeBegin)
  !(TradePeriod'Column TradeDuration)

-- encode the row type of a table with a vanilla ADT
data TradePeriod'Row = TradePeriod'Row
  !(TradePeriod TradeBegin)
  !(TradePeriod TradeDuration)

-- boilerplate code for enumeration of all rows from a table
enumRowsOfTradePeriod
  :: TradePeriod'Table -> (Int -> TradePeriod'Row -> IO ()) -> IO ()
enumRowsOfTradePeriod (TradePeriod'Table (TradePeriod'Column !colTradeBegin) (TradePeriod'Column !colTradeDuration)) !process
  = do
    rowCnt <- countRows
    let go :: Int -> IO ()
        go !row = if row >= rowCnt
          then return ()
          else do
            process row $ TradePeriod'Row (unsafeIndex colTradeBegin row)
                                          (unsafeIndex colTradeDuration row)
            go $ row + 1
    go 0
 where
  countRows :: IO Int
  countRows = do
    let cnt = V.length colTradeBegin
    unless (cnt == V.length colTradeDuration) $ throwIO $ TypeError
      "length mismatch across columns"
    return cnt

-- boilerplate code to retrive a specific row from a table
rowOfTradePeriod :: TradePeriod'Table -> Int -> IO TradePeriod'Row
rowOfTradePeriod (TradePeriod'Table (TradePeriod'Column !colTradeBegin) (TradePeriod'Column !colTradeDuration)) !row
  = do
    rowCnt <- countRows
    unless (row >= 0 && row < rowCnt) $ throwIO $ TypeError
      "row index out of range"
    return $ TradePeriod'Row (unsafeIndex colTradeBegin row)
                             (unsafeIndex colTradeDuration row)
 where
  countRows :: IO Int
  countRows = do
    let cnt = V.length colTradeBegin
    unless (cnt == V.length colTradeDuration) $ throwIO $ TypeError
      "length mismatch across columns"
    return cnt


-- encode row reference from a fact table to a dimension table with an alias
-- of Int
newtype OHLC'TradePeriod = OHLC'TradePeriod Int


type Price = Double

newtype OpenPrice = OpenPrice Price
newtype HighPrice = HighPrice Price
newtype LowPrice = LowPrice Price
newtype ClosePrice  =ClosePrice Price

type family OHLC field where
  OHLC OHLC'TradePeriod = Int
  OHLC OpenPrice = Price
  OHLC HighPrice = Price
  OHLC LowPrice = Price
  OHLC ClosePrice = Price

newtype OHLC'Column field = OHLC'Column
  (Vector (OHLC field))

data OHLC'Table = OHLC'Table
  !(OHLC'Column OHLC'TradePeriod)
  !(OHLC'Column OpenPrice)
  !(OHLC'Column HighPrice)
  !(OHLC'Column LowPrice)
  !(OHLC'Column ClosePrice)

data OHLC'Row = OHLC'Row
  !TradePeriod'Row
  !(OHLC OpenPrice)
  !(OHLC HighPrice)
  !(OHLC LowPrice)
  !(OHLC ClosePrice)

enumRowsOfOHLC
  :: TradePeriod'Table -> OHLC'Table -> (Int -> OHLC'Row -> IO ()) -> IO ()
enumRowsOfOHLC !tabTradePeriod (OHLC'Table (OHLC'Column !col'OHLC'TradePeriod) (OHLC'Column !col'OpenPrice) (OHLC'Column !col'HighPrice) (OHLC'Column !col'LowPrice) (OHLC'Column !col'ClosePrice)) !process
  = do
    rowCnt <- countRows
    let go :: Int -> IO ()
        go !row = if row >= rowCnt
          then return ()
          else do
            rowTradePeriod <- rowOfTradePeriod
              tabTradePeriod
              (unsafeIndex col'OHLC'TradePeriod row)
            process row $ OHLC'Row rowTradePeriod
                                   (unsafeIndex col'OpenPrice row)
                                   (unsafeIndex col'HighPrice row)
                                   (unsafeIndex col'LowPrice row)
                                   (unsafeIndex col'ClosePrice row)
            go $ row + 1
    go 0
 where
  countRows :: IO Int
  countRows = do
    let cnt = V.length col'OHLC'TradePeriod
    unless (cnt == V.length col'OpenPrice) $ throwIO $ TypeError
      "length mismatch across columns"
    unless (cnt == V.length col'HighPrice) $ throwIO $ TypeError
      "length mismatch across columns"
    unless (cnt == V.length col'LowPrice) $ throwIO $ TypeError
      "length mismatch across columns"
    unless (cnt == V.length col'ClosePrice) $ throwIO $ TypeError
      "length mismatch across columns"
    return cnt

rowOfOHLC :: TradePeriod'Table -> OHLC'Table -> Int -> IO OHLC'Row
rowOfOHLC !tabTradePeriod (OHLC'Table (OHLC'Column !col'OHLC'TradePeriod) (OHLC'Column !col'OpenPrice) (OHLC'Column !col'HighPrice) (OHLC'Column !col'LowPrice) (OHLC'Column !col'ClosePrice)) !row
  = do
    rowCnt <- countRows
    unless (row >= 0 && row < rowCnt) $ throwIO $ TypeError
      "row index out of range"
    rowTradePeriod <- rowOfTradePeriod tabTradePeriod
                                       (unsafeIndex col'OHLC'TradePeriod row)
    return $ OHLC'Row rowTradePeriod
                      (unsafeIndex col'OpenPrice row)
                      (unsafeIndex col'HighPrice row)
                      (unsafeIndex col'LowPrice row)
                      (unsafeIndex col'ClosePrice row)
 where
  countRows :: IO Int
  countRows = do
    let cnt = V.length col'OHLC'TradePeriod
    unless (cnt == V.length col'OpenPrice) $ throwIO $ TypeError
      "length mismatch across columns"
    unless (cnt == V.length col'HighPrice) $ throwIO $ TypeError
      "length mismatch across columns"
    unless (cnt == V.length col'LowPrice) $ throwIO $ TypeError
      "length mismatch across columns"
    unless (cnt == V.length col'ClosePrice) $ throwIO $ TypeError
      "length mismatch across columns"
    return cnt


