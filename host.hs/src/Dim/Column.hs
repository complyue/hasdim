
module Dim.Column where

import           Prelude
-- import           Debug.Trace

import           Control.Concurrent.STM

import           Data.Dynamic

import           Language.Edh.EHI

import           Dim.XCHG
import           Dim.DataType


class ManagedColumn a where

  -- | data type of the column
  data'type'of'column :: a -> DataType

  -- obtain a view of the physical storage backing the column data
  --
  -- the underlying storage is mutable anytime, thread safety has to be
  -- guaranteed by proper mediation otherwise, e.g. content to set a
  -- changer attribute to a thread's identity before modifiying a column,
  -- and check such a attribute to be `frozen` valued before allowing the
  -- STM tx to commit
  view'column'data :: a -> STM FlatArray

  -- called when valid data length of the column is requested
  read'column'length :: a -> STM Int

  -- called when a new capacity is requested for the column
  grow'column'capacity :: a -> Int -> (FlatArray -> STM ()) -> EdhTx

  -- called when a new length is marked for the column
  mark'column'length :: a -> Int -> STM () -> EdhTx

  -- called when viewing-slicing is requested for the column
  -- -> Start -> Stop
  -- -> (NotApplicableExit :: STM ()) 
  -- -> (Exit :: (CloneChildren? -> NewColumn -> STM ()))
  -- -> EdhTx
  view'column'slice :: a
    -> Int -> Int -> (Bool -> Column -> STM ()) -> EdhTx

  -- called when copying-slicing is requested for the column
  -- -> Start -> Stop -> Step 
  -- -> (CloneChildren? -> NewColumn -> STM ())
  -- -> EdhTx
  copy'column'slice :: a
    -> Int -> Int -> Int -> (Bool -> Column -> STM ()) -> EdhTx

  -- called when data extraction with a bool index (the mask) is requested
  -- for the column
  -- -> MaskColumn
  -- -> (NotApplicableExit :: STM ()) 
  -- -> (Exit :: (CloneChildren? -> NewColumn -> STM ()))
  -- -> EdhTx
  extract'column'bool :: a
    -> Column -> STM () -> (Bool -> Column -> STM ()) -> EdhTx

  -- called when data extraction with a fancy index is requested for the
  -- column
  -- -> IndexColumn
  -- -> (NotApplicableExit :: STM ()) 
  -- -> (Exit :: (CloneChildren? -> NewColumn -> STM ()))
  -- -> EdhTx
  extract'column'fancy :: a
    -> Column -> STM () -> (Bool -> Column -> STM ()) -> EdhTx


-- | A column is a 1-dimensional array with pre-allocated storage capacity,
-- safely typed for data manipulation.
--
-- 'Column' serves technically as a monomorphic type, wrapping an actually 
-- polymorphically-typed instance value, so as to be the host storage (which
-- has to be monomorphic to be casted to 'Dynamic' value) of an Edh object
-- wrapping it to the scripting surface.
data Column where
  Column ::ManagedColumn a => a -> Column


columnCapacity :: Column -> STM Int
columnCapacity (Column !col) = flatArrayCapacity <$> view'column'data col


unsafeReadColumnCell
  :: EdhThreadState -> Column -> Int -> (EdhValue -> STM ()) -> STM ()
unsafeReadColumnCell !ets (Column !col) !idx !exit = view'column'data col
  >>= \ !cs -> flat'array'read (data'type'of'column col) ets cs idx exit

unsafeWriteColumnCell
  :: EdhThreadState
  -> Column
  -> Int
  -> EdhValue
  -> (EdhValue -> STM ())
  -> STM ()
unsafeWriteColumnCell !ets (Column !col) !idx !val !exit = view'column'data col
  >>= \ !cs -> flat'array'write (data'type'of'column col) ets cs idx val exit

unsafeFillColumn
  :: EdhThreadState -> Column -> EdhValue -> [Int] -> STM () -> STM ()
unsafeFillColumn !ets (Column !col) !val !idxs !exit =
  fromEdh ets val $ \ !sv -> view'column'data col >>= \ !cs -> flat'array'update
    (data'type'of'column col)
    ets
    [ (i, sv) | i <- idxs ]
    cs
    exit


sliceColumn
  :: EdhThreadState
  -> Object
  -> Int
  -> Int
  -> Int
  -> (Int -> Int -> Object -> STM ())
  -> STM ()
sliceColumn !ets !thatCol !start !stop !step !exit =
  castObjectStore thatCol >>= \case
    Nothing -> throwEdh
      ets
      EvalError
      "bug: not a column object passed to unsafeSliceColumn"
    Just (!thisCol, (Column !col)) -> if stop >= start && step == 1
      then
        runEdhTx ets
        $ view'column'slice col start stop
        $ \ !cloneChildren colNew'@(Column !colNew) -> do
            !ccNew <- columnCapacity colNew'
            !clNew <- read'column'length colNew
            if cloneChildren
              then edhCloneHostObj ets thisCol thatCol colNew'
                $ \ !newColObj -> exit ccNew clNew newColObj
              else edhCreateHostObj (edh'obj'class thisCol) (toDyn colNew') []
                >>= \ !newColObj -> exit ccNew clNew newColObj
      else
        runEdhTx ets
        $ copy'column'slice col start stop step
        $ \ !cloneChildren colNew'@(Column !colNew) -> do
            !ccNew <- columnCapacity colNew'
            !clNew <- read'column'length colNew
            if cloneChildren
              then edhCloneHostObj ets thisCol thatCol colNew'
                $ \ !newColObj -> exit ccNew clNew newColObj
              else edhCreateHostObj (edh'obj'class thisCol) (toDyn colNew') []
                >>= \ !newColObj -> exit ccNew clNew newColObj


extractColumnBool
  :: EdhThreadState
  -> Object
  -> Column
  -> STM ()
  -> (Int -> Object -> STM ())
  -> STM ()
extractColumnBool !ets !thatCol !colMask !naExit !exit =
  castObjectStore thatCol >>= \case
    Nothing -> throwEdh
      ets
      EvalError
      "bug: not a column object passed to extractColumnBool"
    Just (!thisCol, (Column !col)) ->
      runEdhTx ets
        $ extract'column'bool col colMask naExit
        $ \ !cloneChildren colNew'@(Column !colNew) ->
            read'column'length colNew >>= \ !clNew -> if cloneChildren
              then edhCloneHostObj ets thisCol thatCol colNew'
                $ \ !newColObj -> exit clNew newColObj
              else edhCreateHostObj (edh'obj'class thisCol) (toDyn colNew') []
                >>= \ !newColObj -> exit clNew newColObj


extractColumnFancy
  :: EdhThreadState
  -> Object
  -> Column
  -> STM ()
  -> (Object -> STM ())
  -> STM ()
extractColumnFancy !ets !thatCol !colIdx !naExit !exit =
  castObjectStore thatCol >>= \case
    Nothing -> throwEdh
      ets
      EvalError
      "bug: not a column object passed to extractColumnBool"
    Just (!thisCol, (Column !col)) ->
      runEdhTx ets
        $ extract'column'fancy col colIdx naExit
        $ \ !cloneChildren !colNew -> if cloneChildren
            then edhCloneHostObj ets thisCol thatCol colNew exit
            else
              edhCreateHostObj (edh'obj'class thisCol) (toDyn colNew) []
                >>= exit

