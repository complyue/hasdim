module Dim.Column where

-- import           Debug.Trace

import Control.Concurrent.STM
import Data.Dynamic
import qualified Data.Text as T
import Data.Typeable hiding (TypeRep, typeRep)
import Dim.DataType
import Dim.XCHG
import Foreign
import Language.Edh.EHI
import Type.Reflection
import Prelude

data InstanceDisposition = StayComposed | ExtractAlone

class
  ( EdhXchg a,
    FlatArray f a,
    Typeable a,
    Typeable (c a),
    Typeable (f a),
    Typeable f,
    Typeable a
  ) =>
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
    c a -> ArrayCapacity -> EdhTxExit (f a, ArrayCapacity) -> EdhTx

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

  derive'new'column ::
    c a ->
    ((f a, ArrayLength, ArrayCapacity) -> ArrayCapacity) ->
    ( forall c' f'.
      ManagedColumn c' f' a =>
      ( (f a, ArrayLength) -> (f' a, ArrayCapacity) -> IO ArrayLength,
        c' a -> IO ()
      )
    ) ->
    IO ()

  -- extract elements by a mask column of the same shape
  extract'column'bool ::
    forall c' f'.
    ManagedColumn c' f' YesNo =>
    c a ->
    c' YesNo ->
    EdhTxExit (InstanceDisposition, c a) ->
    EdhTx

  -- extract elements by an index column
  extract'column'fancy ::
    forall c' f'.
    ManagedColumn c' f' Int =>
    c a ->
    c' Int ->
    EdhTxExit (InstanceDisposition, c a) ->
    EdhTx

data SomeColumn
  = forall c f a.
    ( ManagedColumn c f a,
      Typeable (c a),
      Typeable (f a),
      Typeable f,
      Typeable a
    ) =>
    SomeColumn (TypeRep f) (c a)

someColumn ::
  forall c f a.
  ( ManagedColumn c f a,
    Typeable (c a),
    Typeable (f a),
    Typeable f,
    Typeable a
  ) =>
  c a ->
  SomeColumn
someColumn = SomeColumn (typeRep @f)

asColumnOf ::
  forall a r.
  (Typeable a) =>
  Object ->
  r ->
  (forall c f. ManagedColumn c f a => c a -> r) ->
  r
asColumnOf !obj !naExit !exit = case dynamicHostData obj of
  Nothing -> naExit
  Just dd -> case fromDynamic dd of
    Nothing -> naExit
    Just (SomeColumn _ (col :: c b)) -> case eqT of
      Nothing -> naExit
      Just (Refl :: a :~: b) -> exit col

asColumnOf' ::
  forall a r.
  (Typeable a) =>
  EdhValue ->
  r ->
  (forall c f. ManagedColumn c f a => c a -> r) ->
  r
asColumnOf' !val !naExit !exit = case edhUltimate val of
  EdhObject !obj -> asColumnOf obj naExit exit
  _ -> naExit

withColumnOf ::
  forall a.
  Typeable a =>
  Object ->
  EdhTx ->
  (forall c f. ManagedColumn c f a => Object -> c a -> EdhTx) ->
  EdhTx
withColumnOf !obj naExit !colExit !ets = do
  supers <- readTVar $ edh'obj'supers obj
  withComposition $ obj : supers
  where
    withComposition :: [Object] -> STM ()
    withComposition [] = runEdhTx ets naExit
    withComposition (o : rest) =
      asColumnOf @a o (withComposition rest) (runEdhTx ets . colExit o)

withColumnOf' ::
  forall a.
  Typeable a =>
  EdhValue ->
  EdhTx ->
  (forall c f. ManagedColumn c f a => Object -> c a -> EdhTx) ->
  EdhTx
withColumnOf' !val naExit !colExit = case edhUltimate val of
  EdhObject !obj -> do
    withColumnOf obj naExit colExit
  _ -> naExit

withColumnSelfOf ::
  forall a.
  Typeable a =>
  (forall c f. ManagedColumn c f a => Object -> c a -> EdhTx) ->
  EdhTx
withColumnSelfOf !colExit !ets =
  runEdhTx ets $ withColumnOf @a that naExit colExit
  where
    that = edh'scope'that $ contextScope $ edh'context ets
    naExit =
      throwEdhTx UsageError $
        "not an expected self column of type " <> T.pack (show $ typeRep @a)

withColumnSelf ::
  (forall c f a. ManagedColumn c f a => Object -> c a -> EdhTx) ->
  EdhTx
withColumnSelf !colExit !ets = do
  supers <- readTVar $ edh'obj'supers that
  withComposition $ that : supers
  where
    that = edh'scope'that $ contextScope $ edh'context ets
    naExit = throwEdh ets UsageError "not an expected self column"

    withComposition :: [Object] -> STM ()
    withComposition [] = naExit
    withComposition (o : rest) = case fromDynamic =<< dynamicHostData o of
      Nothing -> withComposition rest
      Just (SomeColumn _ col) -> runEdhTx ets $ colExit o col

getColDtype :: Object -> (Object -> STM ()) -> STM ()
getColDtype !objCol !exit = readTVar (edh'obj'supers objCol) >>= findSuperDto
  where
    findSuperDto :: [Object] -> STM ()
    findSuperDto [] = error "bug: no dtype super for column"
    -- this is right and avoids unnecessary checks in vastly usual cases
    findSuperDto [dto] = exit dto
    -- safe guard in case a Column instance has been further extended
    findSuperDto (maybeDto : rest) =
      withDataType maybeDto (findSuperDto rest) (const $ exit maybeDto)

sliceColumn ::
  forall c f a.
  ManagedColumn c f a =>
  Object ->
  c a ->
  Int ->
  Int ->
  Int ->
  EdhTxExit (Object, c a) ->
  EdhTx
sliceColumn !objCol !col !start !stop !step !exit =
  if stop >= start && step == 1
    then view'column'slice col start stop withSliced
    else copy'column'slice col start stop step withSliced
  where
    withSliced (disp, col') !ets = case disp of
      StayComposed -> edhCloneHostObj ets objCol objCol col' $
        \ !objCol' -> exitEdh ets exit (objCol', col')
      ExtractAlone -> getColDtype objCol $ \ !dto ->
        edhCreateHostObj' (edh'obj'class objCol) (toDyn col') [dto]
          >>= \ !objCol' -> exitEdh ets exit (objCol', col')

extractColumnBool ::
  forall c f a c' f'.
  (ManagedColumn c f a, ManagedColumn c' f' YesNo) =>
  Object ->
  c a ->
  c' YesNo ->
  EdhTxExit (Object, c a) ->
  EdhTx
extractColumnBool !objCol !col !colMask !exit =
  extract'column'bool col colMask $ \(disp, col') !ets -> case disp of
    StayComposed -> edhCloneHostObj ets objCol objCol col' $
      \ !objCol' -> exitEdh ets exit (objCol', col')
    ExtractAlone -> getColDtype objCol $ \ !dto ->
      edhCreateHostObj' (edh'obj'class objCol) (toDyn col') [dto]
        >>= \ !objCol' -> exitEdh ets exit (objCol', col')

extractColumnFancy ::
  forall c f a c' f'.
  (ManagedColumn c f a, ManagedColumn c' f' Int) =>
  Object ->
  c a ->
  c' Int ->
  EdhTxExit (Object, c a) ->
  EdhTx
extractColumnFancy !objCol !col !colIdxs !exit =
  extract'column'fancy col colIdxs $ \(disp, col') !ets -> case disp of
    StayComposed -> edhCloneHostObj ets objCol objCol col' $
      \ !objCol' -> exitEdh ets exit (objCol', col')
    ExtractAlone -> getColDtype objCol $ \ !dto ->
      edhCreateHostObj' (edh'obj'class objCol) (toDyn col') [dto]
        >>= \ !objCol' -> exitEdh ets exit (objCol', col')
