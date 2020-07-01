
module Schema where

import           Prelude
-- import           Debug.Trace

import           Foreign

import           Control.Exception
import           Control.Monad.Reader

import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import qualified Data.Text                     as T
-- import qualified Data.HashMap.Strict           as Map
-- import           Data.Dynamic
-- import           Data.Hashable

import           Data.Vector.Storable          as V

import           Data.Lossless.Decimal         as D

import           Language.Edh.EHI



class EdhXchg t where
  toEdh :: (Storable t) => EdhProgState -> t -> (EdhValue -> STM ()) -> STM ()
  fromEdh :: (Storable t) => EdhProgState  -> EdhValue -> (t -> STM ()) -> STM ()

instance {-# OVERLAPPABLE #-} EdhXchg Double where
  toEdh _pgs !n !exit = exit $ EdhDecimal $ fromRational $ toRational n
  fromEdh _pgs (EdhDecimal !n) !exit = exit $ fromRational $ toRational n
  fromEdh !pgs !v _ =
    throwEdhSTM pgs EvalError $ "Number expected but given a " <> T.pack
      (edhTypeNameOf v)

instance {-# OVERLAPPABLE #-} (Integral a) => EdhXchg a where
  toEdh _pgs !n !exit = exit $ EdhDecimal $ fromRational $ toRational n
  fromEdh !pgs (EdhDecimal !n) !exit = case D.decimalToInteger n of
    Nothing ->
      throwEdhSTM pgs EvalError $ "Not an integer: " <> T.pack (show n)
    Just !i -> exit $ fromInteger i
  fromEdh !pgs !v _ =
    throwEdhSTM pgs EvalError $ "Number expected but given a " <> T.pack
      (edhTypeNameOf v)



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

-- tag for a data field type
type Field t = (EdhXchg t, Storable t) => t
type Column t = (EdhXchg t, Storable t) => Vector t



-- atomic storage data types

type InstrumentId = Text
type TradeTime = Int64
type TradeMinutes = Int32
type Price = Double



-- encode the storage data type of a table as a vanilla ADT
data TradePeriod'Table = TradePeriod'Table {
    meta'TradePeriod'InstruId :: !InstrumentId
  , pk'TradePeriod'Begin :: !(Column TradeTime)
  , col'TradePeriod'Duration :: !(Column TradeMinutes)
  }

-- encode the row type of a table as a vanilla ADT
data TradePeriod'Row = TradePeriod'Row {
    row'TradePeriod'Begin :: !(Field TradeTime)
  , row'TradePeriod'Duration :: !(Field TradeMinutes)
  }

-- implement the Table class
instance Table TradePeriod'Table where
  type RefTables TradePeriod'Table = ()
  type RowType TradePeriod'Table = TradePeriod'Row

  countRows (TradePeriod'Table _ (!colTradeBegin) (!colTradeDuration)) = do
    let cnt = V.length colTradeBegin
    unless (cnt == V.length colTradeDuration) $ throwIO $ TypeError
      "length mismatch across columns"
    return cnt
  getRow () tab@(TradePeriod'Table _ (!colTradeBegin) (!colTradeDuration)) !row
    = do
      rowCnt <- countRows tab
      unless (row >= 0 && row < rowCnt) $ throwIO $ TypeError
        "row index out of range"
      return $ TradePeriod'Row (unsafeIndex colTradeBegin row)
                               (unsafeIndex colTradeDuration row)
  -- boilerplate code to enumerate all rows from a table, eliding
  -- bounds checks for better performance
  enumRows () tab@(TradePeriod'Table _ (!colTradeBegin) (!colTradeDuration)) !process
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
data MinuBar'Table = MinuBar'Table {
    meta'MinuBar'InstruId :: !InstrumentId
    -- single bar span
  , meta'MinuBar'Freq :: !TradeMinutes
    -- reference TradePeriod table
  , fk'MinuBar'TradePeriod'Begin :: !(Column Int)
    -- since period begin
  , col'MinuBar'OpenTime :: !(Column TradeMinutes)
  }

-- row type of minute bar table
data MinuBar'Row = MinuBar'Row {
    ref'MinuBar'TradePeriod :: !TradePeriod'Row
  , row'MinuBar'OpenTime :: !(Field TradeMinutes)
  }

-- implement the Table class
instance Table MinuBar'Table where
  type RefTables MinuBar'Table = TradePeriod'Table
  type RowType MinuBar'Table = MinuBar'Row

  countRows (MinuBar'Table _ _ (!col'MinuBar'TradePeriod) (!col'MinuBarOpen)) =
    do
      let cnt = V.length col'MinuBar'TradePeriod
      unless (cnt == V.length col'MinuBarOpen) $ throwIO $ TypeError
        "length mismatch across columns"
      return cnt
  getRow !tabTradePeriod tab@(MinuBar'Table _ _ (!col'MinuBar'TradePeriod) (!col'MinuBarOpen)) !row
    = do
      rowCnt <- countRows tab
      unless (row >= 0 && row < rowCnt) $ throwIO $ TypeError
        "row index out of range"
      rowTradePeriod <- getRow ()
                               tabTradePeriod
                               (unsafeIndex col'MinuBar'TradePeriod row)
      return $ MinuBar'Row rowTradePeriod (unsafeIndex col'MinuBarOpen row)



-- the storage data type of minute ohlc bar table
data MinuOHLC'Table = MinuOHLC'Table {
    col'MinuOHLC'OpenPrice :: !(Column Price)
  , col'MinuOHLC'HighPrice ::  !(Column Price)
  , col'MinuOHLC'LowPrice ::  !(Column Price)
  , col'MinuOHLC'ClosePrice ::  !(Column Price)
  }

-- row type of minute ohlc bar table
data MinuOHLC'Row = MinuOHLC'Row {
    ref'MinuOHLC'MinuBar :: !MinuBar'Row
  , row'MinuOHLC'OpenPrice :: !(Field Price)
  , row'MinuOHLC'HighPrice ::  !(Field Price)
  , row'MinuOHLC'LowPrice ::  !(Field Price)
  , row'MinuOHLC'ClosePrice ::  !(Field Price)
  }

-- implement the Table class
instance Table MinuOHLC'Table where
  type RefTables MinuOHLC'Table = (TradePeriod'Table, MinuBar'Table)
  type RowType MinuOHLC'Table = MinuOHLC'Row

  countRows (MinuOHLC'Table (!col'OpenPrice) (!col'HighPrice) (!col'LowPrice) (!col'ClosePrice))
    = do
      let cnt = V.length col'OpenPrice
      unless (cnt == V.length col'HighPrice) $ throwIO $ TypeError
        "length mismatch across columns"
      unless (cnt == V.length col'LowPrice) $ throwIO $ TypeError
        "length mismatch across columns"
      unless (cnt == V.length col'ClosePrice) $ throwIO $ TypeError
        "length mismatch across columns"
      return cnt
  getRow (!tabTradePeriod, !tabMinuBar) tab@(MinuOHLC'Table (!col'OpenPrice) (!col'HighPrice) (!col'LowPrice) (!col'ClosePrice)) !row
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
  enumRows (!tabTradePeriod, !tabMinuBar) tab@(MinuOHLC'Table (!col'OpenPrice) (!col'HighPrice) (!col'LowPrice) (!col'ClosePrice)) !process
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

