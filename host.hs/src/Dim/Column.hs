module Dim.Column where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Monad
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
  grow'column'capacity :: c a -> ArrayCapacity -> EdhTxExit () -> EdhTx
  grow'column'capacity col cap exit =
    grow'column'capacity' col cap $ const $ exitEdhTx exit ()

  -- called when a new capacity is requested for the column
  grow'column'capacity' ::
    c a -> ArrayCapacity -> EdhTxExit (f a, ArrayLength) -> EdhTx

  -- called when a new length is marked for the column
  mark'column'length :: c a -> ArrayLength -> EdhTxExit () -> EdhTx

  -- called when viewing-slicing is requested for the column
  view'column'slice ::
    c a ->
    Int -> -- start
    Int -> -- stop
    EdhTxExit (InstanceDisposition, SomeColumn) ->
    EdhTx

  -- called when copying-slicing is requested for the column
  copy'column'slice ::
    c a ->
    Int -> -- capacity
    Int -> -- start
    Int -> -- stop
    Int -> -- step
    EdhTxExit (InstanceDisposition, SomeColumn) ->
    EdhTx

  -- generate another new column by custom deriver & receiver
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
    EdhTxExit SomeColumn ->
    EdhTx

  -- extract elements by an index column
  extract'column'fancy ::
    forall c' f'.
    ManagedColumn c' f' Int =>
    c a ->
    c' Int ->
    EdhTxExit SomeColumn ->
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

withColumn :: Object -> (Object -> SomeColumn -> EdhTx) -> EdhTx
withColumn !colObj =
  withColumn' colObj $
    throwEdhTx UsageError "not a Column as expected"

withColumnSelf :: (Object -> SomeColumn -> EdhTx) -> EdhTx
withColumnSelf !colExit !ets =
  runEdhTx ets $ withColumn' that naExit colExit
  where
    that = edh'scope'that $ contextScope $ edh'context ets
    naExit =
      throwEdhTx UsageError "this is not a Column as expected"

withColumn' :: Object -> EdhTx -> (Object -> SomeColumn -> EdhTx) -> EdhTx
withColumn' !colObj naExit !colExit !ets = do
  supers <- readTVar $ edh'obj'supers colObj
  withComposition $ colObj : supers
  where
    withComposition :: [Object] -> STM ()
    withComposition [] = runEdhTx ets naExit
    withComposition (o : rest) = case fromDynamic =<< dynamicHostData o of
      Nothing -> withComposition rest
      Just col -> runEdhTx ets $ colExit o col

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
  EdhTxExit EdhValue ->
  (forall c f. ManagedColumn c f a => Object -> c a -> EdhTx) ->
  EdhTx
withColumnSelfOf !exit !colExit !ets =
  runEdhTx ets $ withColumnOf @a that naExit colExit
  where
    that = edh'scope'that $ contextScope $ edh'context ets
    naExit = exitEdhTx exit edhNA

getColumnDtype :: EdhThreadState -> Object -> (Object -> STM ()) -> STM ()
getColumnDtype ets !objCol = getColumnDtype' objCol $
  edhSimpleDesc ets (EdhObject objCol) $ \ !badDesc ->
    throwEdh ets UsageError $ "not a Column with dtype: " <> badDesc

getColumnDtype' :: Object -> STM () -> (Object -> STM ()) -> STM ()
getColumnDtype' !objCol naExit !exit =
  readTVar (edh'obj'supers objCol) >>= findSuperDto
  where
    findSuperDto :: [Object] -> STM ()
    findSuperDto [] = naExit
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
  EdhTxExit (Object, SomeColumn) ->
  EdhTx
sliceColumn !objCol !col !start !stop !step !exit =
  if stop >= start && step == 1
    then view'column'slice col start stop withSliced
    else copy'column'slice col stop start stop step withSliced
  where
    withSliced (disp, col') !ets = case disp of
      StayComposed -> edhCloneHostObj ets objCol objCol col' $
        \ !objCol' -> exit (objCol', col') ets
      ExtractAlone -> getColumnDtype ets objCol $ \ !dto ->
        edhCreateHostObj' (edh'obj'class objCol) (toDyn col') [dto]
          >>= \ !objCol' -> exit (objCol', col') ets

extractColumnBool ::
  forall c f a c' f'.
  (ManagedColumn c f a, ManagedColumn c' f' YesNo) =>
  Object ->
  c a ->
  c' YesNo ->
  EdhTxExit (Object, SomeColumn) ->
  EdhTx
extractColumnBool !objCol !col !colMask !exit =
  extract'column'bool col colMask $ \ !col' !ets ->
    getColumnDtype ets objCol $ \ !dto ->
      edhCreateHostObj' (edh'obj'class objCol) (toDyn col') [dto]
        >>= \ !objCol' -> exitEdh ets exit (objCol', col')

extractColumnFancy ::
  forall c f a c' f'.
  (ManagedColumn c f a, ManagedColumn c' f' Int) =>
  Object ->
  c a ->
  c' Int ->
  EdhTxExit (Object, SomeColumn) ->
  EdhTx
extractColumnFancy !objCol !col !colIdxs !exit =
  extract'column'fancy col colIdxs $ \ !col' !ets ->
    getColumnDtype ets objCol $ \ !dto ->
      edhCreateHostObj' (edh'obj'class objCol) (toDyn col') [dto]
        >>= \ !objCol' -> exitEdh ets exit (objCol', col')

idxAssignColumn :: SomeColumn -> EdhValue -> EdhValue -> EdhTx -> EdhTx
idxAssignColumn (SomeColumn _ (col :: c0 a)) !idxVal !tgtVal !doneAssign !ets =
  runEdhTx ets $
    view'column'data col $ \(!cs, !cl) -> do
      let withScalarRHS :: EdhTx
          withScalarRHS = fromEdh @a tgtVal $ \ !rhv -> do
            let byBoolIdx ::
                  forall c f.
                  ManagedColumn c f YesNo =>
                  Object ->
                  c YesNo ->
                  EdhTx
                byBoolIdx _ !idxCol =
                  view'column'data idxCol $ \(idxa, idxl) ->
                    if idxl /= cl
                      then
                        throwEdhTx UsageError $
                          "bool index shape mismatch - "
                            <> T.pack (show idxl)
                            <> " vs "
                            <> T.pack (show cl)
                      else edhContIO $ do
                        let go :: Int -> IO ()
                            go i
                              | i >= idxl = return ()
                              | otherwise = do
                                YesNo yn <- array'reader idxa i
                                when (yn /= 0) $ array'writer cs i rhv
                                go (i + 1)
                        go 0
                        atomically $ runEdhTx ets doneAssign

                byIntpIdx ::
                  forall c f.
                  ManagedColumn c f Int =>
                  Object ->
                  c Int ->
                  EdhTx
                byIntpIdx _ !idxCol = view'column'data idxCol $
                  \(idxa, idxl) -> edhContIO $ do
                    let go :: Int -> IO ()
                        go i
                          | i >= idxl = return ()
                          | otherwise = do
                            idxi <- array'reader idxa i
                            array'writer cs idxi rhv
                            go (i + 1)
                    go 0
                    atomically $ runEdhTx ets doneAssign

                byEdhIdx :: EdhTx
                byEdhIdx _ets = parseEdhIndex ets idxVal $ \case
                  Left !err -> throwEdh ets UsageError err
                  Right !idx -> runEdhTx ets $ do
                    let fillAll :: EdhTx
                        fillAll = edhContIO $ do
                          let go :: Int -> IO ()
                              go i
                                | i >= cl = return ()
                                | otherwise = do
                                  array'writer cs i rhv
                                  go (i + 1)
                          go 0
                          atomically $ runEdhTx ets doneAssign
                    case idx of
                      EdhIndex !i -> edhContIO $ do
                        array'writer cs i rhv
                        atomically $ runEdhTx ets doneAssign
                      EdhAny -> fillAll
                      EdhAll -> fillAll
                      EdhSlice !start !stop !step -> \_ets ->
                        edhRegulateSlice ets cl (start, stop, step) $
                          \(!iStart, !iStop, !iStep) -> runEdhTx ets $
                            edhContIO $ do
                              let go :: Int -> IO ()
                                  go i
                                    | i >= iStop = return ()
                                    | otherwise = do
                                      array'writer cs i rhv
                                      go (i + iStep)
                              go iStart
                              atomically $ runEdhTx ets doneAssign

            withColumnOf' @YesNo
              idxVal
              (withColumnOf' @Int idxVal byEdhIdx byIntpIdx)
              byBoolIdx

      withColumnOf' @a tgtVal withScalarRHS $ \_rhsColInst !rhsCol ->
        view'column'data rhsCol $ \(cs'rhs, cl'rhs) -> do
          let byBoolIdx ::
                forall c f.
                ManagedColumn c f YesNo =>
                Object ->
                c YesNo ->
                EdhTx
              byBoolIdx _ !idxCol =
                if cl'rhs /= cl
                  then
                    throwEdhTx UsageError $
                      "rhs column shape mismatch - "
                        <> T.pack (show cl'rhs)
                        <> " vs "
                        <> T.pack (show cl)
                  else view'column'data idxCol $ \(idxa, idxl) ->
                    if idxl /= cl
                      then
                        throwEdhTx UsageError $
                          "bool index shape mismatch - "
                            <> T.pack (show idxl)
                            <> " vs "
                            <> T.pack (show cl)
                      else edhContIO $ do
                        let go :: Int -> IO ()
                            go i
                              | i >= idxl = return ()
                              | otherwise = do
                                YesNo yn <- array'reader idxa i
                                when (yn /= 0) $
                                  array'reader cs'rhs i
                                    >>= array'writer cs i
                                go (i + 1)
                        go 0
                        atomically $ runEdhTx ets doneAssign

              byIntpIdx ::
                forall c f.
                ManagedColumn c f Int =>
                Object ->
                c Int ->
                EdhTx
              byIntpIdx _ !idxCol = view'column'data idxCol $
                \(idxa, idxl) ->
                  if cl'rhs /= idxl
                    then
                      throwEdhTx UsageError $
                        "rhs column shape mismatch fancy index - "
                          <> T.pack (show cl'rhs)
                          <> " vs "
                          <> T.pack (show idxl)
                    else edhContIO $ do
                      let go :: Int -> IO ()
                          go i
                            | i >= idxl = return ()
                            | otherwise = do
                              idxi <- array'reader idxa i
                              array'reader cs'rhs i
                                >>= array'writer cs idxi
                              go (i + 1)
                      go 0
                      atomically $ runEdhTx ets doneAssign

              byEdhIdx :: EdhTx
              byEdhIdx _ets = parseEdhIndex ets idxVal $ \case
                Left !err -> throwEdh ets UsageError err
                Right !idx -> runEdhTx ets $ case idx of
                  EdhIndex _i ->
                    throwEdhTx
                      UsageError
                      "can not index-assign a rhs column by scalar index"
                  EdhAny ->
                    throwEdhTx
                      UsageError
                      "can not index-assign a rhs column by Any index"
                  EdhAll ->
                    if cl'rhs /= cl
                      then
                        throwEdhTx UsageError $
                          "rhs column shape mismatch - "
                            <> T.pack (show cl'rhs)
                            <> " vs "
                            <> T.pack (show cl)
                      else edhContIO $ do
                        let go :: Int -> IO ()
                            go i
                              | i >= cl = return ()
                              | otherwise = do
                                array'reader cs'rhs i
                                  >>= array'writer cs i
                                go (i + 1)
                        go 0
                        atomically $ runEdhTx ets doneAssign
                  EdhSlice !start !stop !step -> \_ets ->
                    edhRegulateSlice ets cl (start, stop, step) $
                      \(!iStart, !iStop, !iStep) ->
                        if cl'rhs < ((iStop - iStart) `quot` iStep)
                          then
                            throwEdh ets UsageError $
                              "rhs column shape mismatch slicing index - "
                                <> T.pack (show cl'rhs)
                                <> " vs "
                                <> T.pack
                                  ( show iStart <> ":" <> show iStop <> ":"
                                      <> show iStep
                                  )
                          else runEdhTx ets $
                            edhContIO $ do
                              let go :: Int -> Int -> IO ()
                                  go i n
                                    | i >= iStop = return ()
                                    | otherwise = do
                                      array'reader cs'rhs n
                                        >>= array'writer cs i
                                      go (i + iStep) (n + 1)
                              go iStart 0
                              atomically $ runEdhTx ets doneAssign

          withColumnOf' @YesNo
            idxVal
            (withColumnOf' @Int idxVal byEdhIdx byIntpIdx)
            byBoolIdx
