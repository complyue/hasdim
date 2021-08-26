module Dim.Column where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Monad
import Data.Dynamic
import Data.Function
import Data.String
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import Data.Typeable hiding (TypeRep, typeRep)
import Dim.DataType
import Dim.XCHG
import Foreign
import Language.Edh.EHI
import Type.Reflection
import Prelude

data ColumnOf a = forall c f. ManagedColumn c f a => ColumnOf (c a) !Object

instance Typeable a => ScriptArgAdapter (ColumnOf a) where
  adaptEdhArg !v !exit = case edhUltimate v of
    EdhObject o -> withColumnOf @a o badVal $ \_colInst !col ->
      exit $ ColumnOf @a col o
    _ -> badVal
    where
      badVal = edhValueDescTx v $ \ !badDesc ->
        throwEdhTx UsageError $
          T.pack (show $ typeRep @a) <> " Column expected but given: "
            <> badDesc

  adaptedArgValue (ColumnOf _col !obj) = EdhObject obj

instance Eq (ColumnOf a) where
  (ColumnOf _x'col x'o) == (ColumnOf _y'col y'o) = x'o == y'o

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
  view'column'data :: c a -> ((f a, ArrayLength) -> IO ()) -> IO ()

  -- called when valid data length of the column is requested
  read'column'length :: c a -> IO ArrayLength

  -- called when a new capacity is requested for the column
  grow'column'capacity ::
    c a -> ArrayCapacity -> ((f a, ArrayLength) -> IO ()) -> IO ()

  -- called when a new length is marked for the column
  mark'column'length :: c a -> ArrayLength -> IO ()

  -- called when viewing-slicing is requested for the column
  view'column'slice ::
    c a ->
    Int -> -- start
    Int -> -- stop
    ((InstanceDisposition, SomeColumn) -> IO ()) ->
    IO ()

  -- called when copying-slicing is requested for the column
  copy'column'slice ::
    c a ->
    Int -> -- capacity
    Int -> -- start
    Int -> -- stop
    Int -> -- step
    ((InstanceDisposition, SomeColumn) -> IO ()) ->
    IO ()

  -- generate another new column by custom deriver & receiver
  derive'new'column ::
    c a ->
    ((f a, ArrayLength, ArrayCapacity) -> ArrayCapacity) ->
    ( forall c' f'.
      ( ManagedColumn c' f' a,
        Typeable (c' a),
        Typeable (f' a),
        Typeable c',
        Typeable f',
        Typeable a
      ) =>
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
    (SomeColumn -> IO ()) ->
    IO ()

  -- extract elements by an index column
  extract'column'fancy ::
    forall c' f'.
    ManagedColumn c' f' Int =>
    c a ->
    c' Int ->
    (SomeColumn -> IO ()) ->
    IO ()

data SomeColumn
  = forall c f a.
    ( ManagedColumn c f a,
      Typeable (c a),
      Typeable (f a),
      Typeable c,
      Typeable f,
      Typeable a
    ) =>
    SomeColumn (TypeRep f) (c a)

someColumn ::
  forall c f a.
  ( ManagedColumn c f a,
    Typeable (c a),
    Typeable (f a),
    Typeable c,
    Typeable f,
    Typeable a
  ) =>
  c a ->
  SomeColumn
someColumn = SomeColumn (typeRep @f)

castColumn ::
  forall c a f.
  ( ManagedColumn c f a,
    Typeable (c a),
    Typeable (f a),
    Typeable c,
    Typeable f,
    Typeable a
  ) =>
  SomeColumn ->
  Maybe (c a)
castColumn (SomeColumn _ (col :: c' a')) = case eqT of
  Just (Refl :: c' a' :~: c a) -> Just col
  Nothing -> Nothing

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
  Object ->
  SomeColumn ->
  Int ->
  Int ->
  Int ->
  EdhTxExit (Object, SomeColumn) ->
  EdhTx
sliceColumn !objCol (SomeColumn _ !col) !start !stop !step !exit !ets =
  runEdhTx ets $
    edhContIO $
      atomically . withSliced
        & if stop >= start && step == 1
          then view'column'slice col start stop
          else copy'column'slice col stop start stop step
  where
    withSliced (disp, col') = case disp of
      StayComposed -> edhCloneHostObj ets objCol objCol col' $
        \ !objCol' -> runEdhTx ets $ exit (objCol', col')
      ExtractAlone -> getColumnDtype ets objCol $ \ !dto ->
        edhCreateHostObj' (edh'obj'class objCol) (toDyn col') [dto]
          >>= \ !objCol' -> runEdhTx ets $ exit (objCol', col')

extractColumnBool ::
  forall c' f'.
  (ManagedColumn c' f' YesNo) =>
  Object ->
  SomeColumn ->
  c' YesNo ->
  EdhTxExit (Object, SomeColumn) ->
  EdhTx
extractColumnBool !objCol (SomeColumn _ !col) !colMask !exit !ets =
  runEdhTx ets $
    edhContIO $
      extract'column'bool col colMask $ \ !col' -> atomically $
        getColumnDtype ets objCol $ \ !dto ->
          edhCreateHostObj' (edh'obj'class objCol) (toDyn col') [dto]
            >>= \ !objCol' -> exitEdh ets exit (objCol', col')

extractColumnFancy ::
  forall c' f'.
  (ManagedColumn c' f' Int) =>
  Object ->
  SomeColumn ->
  c' Int ->
  EdhTxExit (Object, SomeColumn) ->
  EdhTx
extractColumnFancy !objCol (SomeColumn _ !col) !colIdxs !exit !ets =
  runEdhTx ets $
    edhContIO $
      extract'column'fancy col colIdxs $ \ !col' -> atomically $
        getColumnDtype ets objCol $ \ !dto ->
          edhCreateHostObj' (edh'obj'class objCol) (toDyn col') [dto]
            >>= \ !objCol' -> exitEdh ets exit (objCol', col')

idxAssignColumn :: SomeColumn -> EdhValue -> EdhValue -> EdhTx -> EdhTx
idxAssignColumn (SomeColumn _ (col :: c0 a)) !idxVal !tgtVal !doneAssign !ets =
  runEdhTx ets $
    edhContIO $
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
                    edhContIO $
                      view'column'data idxCol $ \(idxa, idxl) ->
                        if idxl /= cl
                          then
                            atomically $
                              throwEdh ets UsageError $
                                "bool index shape mismatch - "
                                  <> T.pack (show idxl)
                                  <> " vs "
                                  <> T.pack (show cl)
                          else do
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
                  byIntpIdx _ !idxCol =
                    edhContIO $
                      view'column'data idxCol $ \(idxa, idxl) -> do
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

        atomically $
          runEdhTx ets $
            withColumnOf' @a tgtVal withScalarRHS $
              \_rhsColInst !rhsCol ->
                edhContIO $
                  view'column'data rhsCol $ \(cs'rhs, cl'rhs) -> do
                    let byBoolIdx ::
                          forall c f.
                          ManagedColumn c f YesNo =>
                          Object ->
                          c YesNo ->
                          EdhTx
                        byBoolIdx _ !idxCol =
                          edhContIO $
                            if cl'rhs /= cl
                              then
                                atomically $
                                  throwEdh ets UsageError $
                                    "rhs column shape mismatch - "
                                      <> T.pack (show cl'rhs)
                                      <> " vs "
                                      <> T.pack (show cl)
                              else view'column'data idxCol $ \(idxa, idxl) ->
                                if idxl /= cl
                                  then
                                    atomically $
                                      throwEdh ets UsageError $
                                        "bool index shape mismatch - "
                                          <> T.pack (show idxl)
                                          <> " vs "
                                          <> T.pack (show cl)
                                  else do
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
                        byIntpIdx _ !idxCol =
                          edhContIO $
                            view'column'data idxCol $ \(idxa, idxl) ->
                              if cl'rhs /= idxl
                                then
                                  atomically $
                                    throwEdh ets UsageError $
                                      "rhs column shape mismatch fancy index - "
                                        <> T.pack (show cl'rhs)
                                        <> " vs "
                                        <> T.pack (show idxl)
                                else do
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

                    atomically $
                      runEdhTx ets $
                        withColumnOf' @YesNo
                          idxVal
                          (withColumnOf' @Int idxVal byEdhIdx byIntpIdx)
                          byBoolIdx

-- * implementation details for pretty showing of column data

data Text2Show = Text2Show
  { text'to'show :: TL.Text,
    text'len :: Int64
  }

-- todo forbid '\n' '\r', handle '\t', handle wide chars, etc.

text2Show :: Text -> Text2Show
text2Show t = Text2Show t' (TL.length t')
  where
    t' = TL.fromStrict t

instance IsString Text2Show where
  fromString s = Text2Show t $ TL.length t
    where
      t = fromString s

instance Semigroup Text2Show where
  (Text2Show x't x'l) <> (Text2Show y't y'l) =
    Text2Show (x't <> y't) (x'l + y'l)

instance Monoid Text2Show where
  mempty = Text2Show "" 0

data Line2Show = Line2Show
  { line'to'show :: Text2Show,
    first'elem'idx :: Int,
    last'elem'idx :: Int
  }

showColContent ::
  ArrayLength ->
  (ArrayIndex -> (Text -> IO ()) -> IO ()) ->
  (Text -> IO ()) ->
  IO ()
showColContent !cl !readElem !exit = tryHeadLines [] 0 0 "" 0
  where
    -- todo make these tunable
    lineWidth = 79
    maxHeadLines = 10

    tryHeadLines ::
      [Line2Show] -> Int -> ArrayIndex -> Text2Show -> ArrayIndex -> IO ()
    tryHeadLines cumLines nLines i line lineFirstElemIdx
      -- got all elements
      | i >= cl =
        if nLines <= 0
          then exit $ TL.toStrict $ text'to'show line
          else do
            let cumLines' =
                  if text'len line > 0
                    then Line2Show line lineFirstElemIdx (cl - 1) : cumLines
                    else cumLines
                headLines = concat $ fancyLine <$> reverse cumLines'
            exit $ TL.toStrict $ TL.unlines headLines

      -- more elements to show
      | nLines >= maxHeadLines = do
        showTailLines (reverse cumLines) (lineFirstElemIdx - 1)

      -- one more element to add
      | otherwise = readElem i $ \ !elemTxt -> do
        let elemFrag = text2Show elemTxt <> ", "
            line' = line <> elemFrag
        if text'len line' > lineWidth
          then
            tryHeadLines
              ( Line2Show line lineFirstElemIdx (i - 1) :
                cumLines
              )
              (nLines + 1)
              (i + 1)
              elemFrag
              i
          else tryHeadLines cumLines nLines (i + 1) line' lineFirstElemIdx

    showTailLines :: [Line2Show] -> ArrayIndex -> IO ()
    showTailLines hls headIdxShown = go [] 0 (cl - 1) "" (cl - 1)
      where
        go ::
          [Line2Show] -> Int -> ArrayIndex -> Text2Show -> ArrayIndex -> IO ()
        go cumLines nLines i line lineLastElemIdx
          -- not that many elements, we can show its entirty
          | i <= headIdxShown = do
            let cumLines' = Line2Show line (i + 1) lineLastElemIdx : cumLines
                headLines = concat $ fancyLine <$> hls
                tailLines = concat $ fancyLine <$> cumLines'
            exit $ TL.toStrict $ TL.unlines $ headLines ++ tailLines

          -- more elements then we'd show
          | nLines >= maxHeadLines = do
            let headLines = concat $ fancyLine <$> hls
                tailLines = concat $ fancyLine <$> cumLines
            exit $
              TL.toStrict $ TL.unlines $ headLines ++ [" ... "] ++ tailLines

          -- one more element to add
          | otherwise = readElem i $ \ !elemTxt -> do
            let elemFrag = text2Show elemTxt <> ", "
                line' = elemFrag <> line
            if text'len line' > lineWidth
              then
                go
                  ( Line2Show line (i + 1) lineLastElemIdx :
                    cumLines
                  )
                  (nLines + 1)
                  (i - 1)
                  elemFrag
                  i
              else go cumLines nLines (i - 1) line' lineLastElemIdx

    fancyLine :: Line2Show -> [TL.Text]
    fancyLine (Line2Show (Text2Show txt _) firstIdx lastIdx) =
      [ "# " <> TL.pack (show firstIdx) <> " ~ " <> TL.pack (show lastIdx),
        txt
      ]
