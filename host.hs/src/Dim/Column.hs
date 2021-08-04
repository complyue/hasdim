module Dim.Column where

-- import           Debug.Trace

import Control.Concurrent.STM
import Data.Dynamic
import qualified Data.Text as T
import Dim.DataType
import Dim.XCHG
import Foreign
import Language.Edh.Curry
import Language.Edh.EHI
import Type.Reflection (typeRep)
import Prelude

class ManagedColumn t where
  -- | data type of the column
  data'type'of'column :: t -> DataType

  -- obtain a view of the physical storage backing the column data
  --
  -- the underlying storage is mutable anytime, thread safety has to be
  -- guaranteed by proper mediation otherwise, e.g. content to set a
  -- changer attribute to a thread's identity before modifiying a column,
  -- and check such a attribute to be `frozen` valued before allowing the
  -- STM tx to commit
  view'column'data :: t -> STM FlatArray

  -- called when valid data length of the column is requested
  read'column'length :: t -> STM Int

  -- called when a new capacity is requested for the column
  grow'column'capacity :: t -> Int -> (FlatArray -> STM ()) -> EdhTx

  -- called when a new length is marked for the column
  mark'column'length :: t -> Int -> STM () -> EdhTx

  -- called when viewing-slicing is requested for the column
  -- -> Start -> Stop
  -- -> (NotApplicableExit :: STM ())
  -- -> (Exit :: (StayComposed? -> NewColumn -> STM ()))
  -- -> EdhTx
  view'column'slice ::
    t ->
    Int ->
    Int ->
    (Bool -> Column -> STM ()) ->
    EdhTx

  -- called when copying-slicing is requested for the column
  -- -> Start -> Stop -> Step
  -- -> (StayComposed? -> NewColumn -> STM ())
  -- -> EdhTx
  copy'column'slice ::
    t ->
    Int ->
    Int ->
    Int ->
    (Bool -> Column -> STM ()) ->
    EdhTx

  -- called when data extraction with a bool index (the mask) is requested
  -- for the column
  -- -> MaskColumn
  -- -> (NotApplicableExit :: STM ())
  -- -> (Exit :: (StayComposed? -> NewColumn -> STM ()))
  -- -> EdhTx
  extract'column'bool ::
    t ->
    Column ->
    STM () ->
    (Bool -> Column -> STM ()) ->
    EdhTx

  -- called when data extraction with a fancy index is requested for the
  -- column
  -- -> IndexColumn
  -- -> (NotApplicableExit :: STM ())
  -- -> (Exit :: (StayComposed? -> NewColumn -> STM ()))
  -- -> EdhTx
  extract'column'fancy ::
    t ->
    Column ->
    STM () ->
    (Bool -> Column -> STM ()) ->
    EdhTx

-- | A column is a 1-dimensional array with pre-allocated storage capacity,
-- safely typed for data manipulation.
--
-- 'Column' serves technically as a monomorphic type, wrapping an actually
-- polymorphically-typed instance value, so as to be the host storage (which
-- has to be monomorphic to be casted to 'Dynamic' value) of an Edh object
-- wrapping it to the scripting surface.
data Column where
  Column :: (Typeable t, ManagedColumn t) => t -> Column

columnCapacity :: Column -> STM Int
columnCapacity (Column !mcol) = flatArrayCapacity <$> view'column'data mcol

columnDataType :: Column -> DataType
columnDataType (Column !mcol) = data'type'of'column mcol

viewColumnData :: Column -> STM FlatArray
viewColumnData (Column !mcol) = view'column'data mcol

readColumnLength :: Column -> STM Int
readColumnLength (Column !mcol) = read'column'length mcol

growColumnCapacity :: Column -> Int -> (FlatArray -> STM ()) -> EdhTx
growColumnCapacity (Column !mcol) = grow'column'capacity mcol

markColumnLength :: Column -> Int -> STM () -> EdhTx
markColumnLength (Column !mcol) = mark'column'length mcol

unsafeReadColumnCell ::
  EdhThreadState -> Column -> Int -> (EdhValue -> STM ()) -> STM ()
unsafeReadColumnCell !ets (Column !col) !idx !exit =
  view'column'data col
    >>= \ !cs -> flat'array'read (data'type'of'column col) ets cs idx exit

unsafeWriteColumnCell ::
  EdhThreadState ->
  Column ->
  Int ->
  EdhValue ->
  (EdhValue -> STM ()) ->
  STM ()
unsafeWriteColumnCell !ets (Column !col) !idx !val !exit =
  view'column'data col
    >>= \ !cs -> flat'array'write (data'type'of'column col) ets cs idx val exit

unsafeFillColumn ::
  EdhThreadState -> Column -> EdhValue -> [Int] -> STM () -> STM ()
unsafeFillColumn !ets (Column !col) !val !idxs !exit =
  fromEdh ets val $ \ !sv ->
    view'column'data col >>= \ !cs ->
      flat'array'update
        (data'type'of'column col)
        ets
        [(i, sv) | i <- idxs]
        cs
        exit

sliceColumn ::
  EdhThreadState ->
  Object ->
  Int ->
  Int ->
  Int ->
  (Int -> Int -> Object -> STM ()) ->
  STM ()
sliceColumn !ets !thatCol !start !stop !step !exit =
  castObjectStore thatCol >>= \case
    Nothing ->
      throwEdh
        ets
        EvalError
        "bug: not a column object passed to sliceColumn"
    Just (!thisCol, Column !col) ->
      if stop >= start && step == 1
        then runEdhTx ets $
          view'column'slice col start stop $
            \ !stayComposed colNew'@(Column !colNew) -> do
              !ccNew <- columnCapacity colNew'
              !clNew <- read'column'length colNew
              if stayComposed
                then edhCloneHostObj ets thisCol thatCol colNew' $
                  \ !newColObj -> exit ccNew clNew newColObj
                else
                  edhCreateHostObj (edh'obj'class thisCol) colNew'
                    >>= \ !newColObj -> exit ccNew clNew newColObj
        else runEdhTx ets $
          copy'column'slice col start stop step $
            \ !stayComposed colNew'@(Column !colNew) -> do
              !ccNew <- columnCapacity colNew'
              !clNew <- read'column'length colNew
              if stayComposed
                then edhCloneHostObj ets thisCol thatCol colNew' $
                  \ !newColObj -> exit ccNew clNew newColObj
                else
                  edhCreateHostObj (edh'obj'class thisCol) colNew'
                    >>= \ !newColObj -> exit ccNew clNew newColObj

copyColumn ::
  EdhThreadState ->
  Object ->
  (Object -> STM ()) ->
  STM ()
copyColumn !ets !thatCol !exit =
  castObjectStore thatCol >>= \case
    Nothing ->
      throwEdh
        ets
        EvalError
        "bug: not a column object passed to copyColumn"
    Just (!thisCol, Column !col) -> do
      !clLen <- read'column'length col
      runEdhTx ets $
        copy'column'slice col 0 clLen 1 $
          \ !stayComposed colNew -> do
            if stayComposed
              then edhCloneHostObj ets thisCol thatCol colNew $
                \ !newColObj -> exit newColObj
              else
                edhCreateHostObj (edh'obj'class thisCol) colNew
                  >>= \ !newColObj -> exit newColObj

extractColumnBool ::
  EdhThreadState ->
  Object ->
  Column ->
  STM () ->
  (Int -> Object -> STM ()) ->
  STM ()
extractColumnBool !ets !thatCol !colMask !naExit !exit =
  castObjectStore thatCol >>= \case
    Nothing ->
      throwEdh
        ets
        EvalError
        "bug: not a column object passed to extractColumnBool"
    Just (!thisCol, Column !col) ->
      runEdhTx ets $
        extract'column'bool col colMask naExit $
          \ !stayComposed colNew'@(Column !colNew) ->
            read'column'length colNew >>= \ !clNew ->
              if stayComposed
                then edhCloneHostObj ets thisCol thatCol colNew' $
                  \ !newColObj -> exit clNew newColObj
                else
                  edhCreateHostObj (edh'obj'class thisCol) colNew'
                    >>= \ !newColObj -> exit clNew newColObj

extractColumnFancy ::
  EdhThreadState ->
  Object ->
  Column ->
  STM () ->
  (Object -> STM ()) ->
  STM ()
extractColumnFancy !ets !thatCol !colIdx !naExit !exit =
  castObjectStore thatCol >>= \case
    Nothing ->
      throwEdh
        ets
        EvalError
        "bug: not a column object passed to extractColumnBool"
    Just (!thisCol, Column !col) ->
      runEdhTx ets $
        extract'column'fancy col colIdx naExit $
          \ !stayComposed !colNew ->
            if stayComposed
              then edhCloneHostObj ets thisCol thatCol colNew exit
              else
                edhCreateHostObj (edh'obj'class thisCol) colNew
                  >>= exit

data ColumnOf t = ColumnOf !Column !Object

typedColumn :: forall t. ColumnOf t -> Column
typedColumn (ColumnOf col _obj) = col

instance Typeable t => ScriptArgAdapter (ColumnOf t) where
  adaptEdhArg !v !exit = case edhUltimate v of
    EdhObject o -> case edh'obj'store o of
      HostStore dd -> case fromDynamic dd of
        Just col@(Column !mcol) -> do
          let dt = data'type'of'column mcol
          if isDataTypeFor @t dt
            then exitEdhTx exit $ ColumnOf col o
            else
              throwEdhTx UsageError $
                "wrong dtype for "
                  <> T.pack (show $ typeRep @t)
                  <> ": "
                  <> data'type'identifier dt
        Nothing -> badVal
      _ -> badVal
    _ -> badVal
    where
      badVal = edhValueDescTx v $ \ !badDesc ->
        throwEdhTx UsageError $
          "Column of dtype="
            <> T.pack (show $ typeRep @t)
            <> " expected but given: "
            <> badDesc

  adaptedArgValue (ColumnOf _col !obj) = EdhObject obj
