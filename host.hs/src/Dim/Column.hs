module Dim.Column where

-- import           Debug.Trace

import Control.Concurrent.STM
import Data.Dynamic
import qualified Data.Text as T
import Data.Typeable hiding (typeRep)
import Dim.DataType
import Dim.XCHG
import Foreign
import Language.Edh.EHI
import Type.Reflection
import Prelude

data InstanceDisposition = StayComposed | ExtractAlone

class
  (EdhXchg a, FlatArray f a, Typeable a, Typeable (c a), Typeable (f a)) =>
  ManagedColumn c f a
    | c -> f
  where
  -- obtain a view of the physical storage backing the column data
  --
  -- the underlying storage is mutable anytime, thread safety has to be
  -- guaranteed by proper mediation otherwise, e.g. content to set a
  -- changer attribute to a thread's identity before modifiying a column
  -- and check such a attribute to be `frozen` valued before allowing the
  -- STM tx to commit
  view'column'data :: c a -> EdhTxExit (f a, ArrayLength) -> EdhTx

  -- called when valid data length of the column is requested
  read'column'length :: c a -> EdhTxExit ArrayLength -> EdhTx

  -- called when a new capacity is requested for the column
  grow'column'capacity ::
    c a -> ArrayCapacity -> EdhTxExit (f a, ArrayLength) -> EdhTx

  -- called when a new length is marked for the column
  mark'column'length :: c a -> ArrayLength -> EdhTxExit () -> EdhTx

  -- called when viewing-slicing is requested for the column
  view'column'slice ::
    c a ->
    Int -> -- start
    Int -> -- stop
    EdhTxExit (InstanceDisposition, c a) ->
    EdhTx

  -- called when copying-slicing is requested for the column
  copy'column'slice ::
    c a ->
    Int -> -- start
    Int -> -- stop
    Int -> -- step
    EdhTxExit (InstanceDisposition, c a) ->
    EdhTx

data SomeColumn
  = forall c f a.
    ( ManagedColumn c f a,
      Typeable (c a),
      Typeable (f a),
      Typeable a
    ) =>
    SomeColumn (c a)

withColumnOf ::
  forall a m.
  (Monad m, Typeable a) =>
  Object ->
  m () ->
  (forall c f. ManagedColumn c f a => c a -> m ()) ->
  m ()
withColumnOf !obj !naExit !exit = case dynamicHostData obj of
  Nothing -> naExit
  Just dd -> case fromDynamic dd of
    Nothing -> naExit
    Just (SomeColumn (col :: c b)) -> case eqT of
      Nothing -> naExit
      Just (Refl :: a :~: b) -> exit col

withColObj ::
  forall m.
  Monad m =>
  Object ->
  m () ->
  (forall c f a. ManagedColumn c f a => c a -> m ()) ->
  m ()
withColObj !obj naExit !exit = case dynamicHostData obj of
  Nothing -> naExit
  Just dd -> case fromDynamic dd of
    Nothing -> naExit
    Just (SomeColumn col) -> exit col

withThisColObj ::
  EdhThreadState ->
  (forall c f a. ManagedColumn c f a => (Object, c a) -> STM ()) ->
  STM ()
withThisColObj !ets !exit = withColObj this nac $ \ !col -> exit (this, col)
  where
    this = edh'scope'this $ contextScope $ edh'context ets
    nac = throwEdh ets EvalError "bug: non-column object of Column class"

{-
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
-}
