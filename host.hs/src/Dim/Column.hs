module Dim.Column where

-- import           Debug.Trace

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
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
import Language.Edh.MHI
import Type.Reflection
import Prelude

-- * Host arg adapter for columns

data ColumnOf a = forall c f. ManagedColumn c f a => ColumnOf (c a) !Object

instance Typeable a => ComputArgAdapter (ColumnOf a) where
  adaptEdhArg !v = (<|> badVal) $ case edhUltimate v of
    EdhObject o ->
      withColumnOf @a o $ \_colInst !col -> return $ ColumnOf @a col o
    _ -> mzero
    where
      badVal = do
        !badDesc <- edhValueDescM v
        throwEdhM UsageError $
          T.pack (show $ typeRep @a) <> " Column expected but given: "
            <> badDesc

  adaptedArgValue (ColumnOf _col !obj) = EdhObject obj

instance Eq (ColumnOf a) where
  (ColumnOf _x'col x'o) == (ColumnOf _y'col y'o) = x'o == y'o

-- * Type class for managed column

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
  view'column'data :: c a -> EIO (f a, ArrayLength)

  -- called when valid data length of the column is requested
  read'column'length :: c a -> EIO ArrayLength

  -- called when a new capacity is requested for the column
  grow'column'capacity :: c a -> ArrayCapacity -> EIO (f a, ArrayLength)

  -- called when a new length is marked for the column
  mark'column'length :: c a -> ArrayLength -> EIO ()

  -- called when viewing-slicing is requested for the column
  view'column'slice ::
    c a ->
    Int -> -- start
    Int -> -- stop
    EIO (InstanceDisposition, SomeColumn)

  -- called when copying-slicing is requested for the column
  copy'column'slice ::
    c a ->
    Int -> -- capacity
    Int -> -- start
    Int -> -- stop
    Int -> -- step
    EIO (InstanceDisposition, SomeColumn)

  -- generate another new column by custom deriver & receiver
  derive'new'column ::
    c a ->
    ((f a, ArrayLength, ArrayCapacity) -> ArrayCapacity) ->
    ( forall f'.
      (FlatArray f' a, Typeable f') =>
      (f a, ArrayLength) ->
      (f' a, ArrayCapacity) ->
      EIO ArrayLength
    ) ->
    EIO SomeColumn

  -- extract elements by a mask column of the same shape
  extract'column'bool ::
    forall c' f'.
    ManagedColumn c' f' YesNo =>
    c a ->
    c' YesNo ->
    EIO SomeColumn

  -- extract elements by an index column
  extract'column'fancy ::
    forall c' f'.
    ManagedColumn c' f' Int =>
    c a ->
    c' Int ->
    EIO SomeColumn

-- * Heterogeneous host wrapper of columns

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

-- * Scripting helper utilities for columns

withColumnSelf :: forall r. (Object -> SomeColumn -> Edh r) -> Edh r
withColumnSelf withCol = do
  !that <- edh'scope'that . contextScope . edh'context <$> edhThreadState
  withColumn that withCol
    <|> throwEdhM EvalError "bug: not a Column self as expected"

{- HLINT ignore "Redundant <$>" -}

withColumn :: forall r. Object -> (Object -> SomeColumn -> Edh r) -> Edh r
withColumn !obj withCol = do
  (obj :) <$> readTVarEdh (edh'obj'supers obj) >>= withComposition
  where
    withComposition :: [Object] -> Edh r
    withComposition [] = naM "not an expected Column object"
    withComposition (o : rest) = case fromDynamic =<< dynamicHostData o of
      Nothing -> withComposition rest
      Just col -> withCol o col

asColumnOf ::
  forall a r.
  (Typeable a) =>
  Object ->
  (forall c f. ManagedColumn c f a => c a -> Edh r) ->
  Edh r
asColumnOf !obj !act = case dynamicHostData obj of
  Nothing -> naAct
  Just dd -> case fromDynamic dd of
    Nothing -> naAct
    Just (SomeColumn _ (col :: c b)) -> case eqT of
      Nothing -> naAct
      Just (Refl :: a :~: b) -> act col
  where
    naAct =
      naM $ "not expected Column of type: " <> T.pack (show $ typeRep @a)

asColumnOf' ::
  forall a r.
  (Typeable a) =>
  EdhValue ->
  (forall c f. ManagedColumn c f a => c a -> Edh r) ->
  Edh r
asColumnOf' !val !act = case edhUltimate val of
  EdhObject !obj -> asColumnOf obj act
  _ ->
    naM $
      "not expected Column object of type: " <> T.pack (show $ typeRep @a)

withColumnOf ::
  forall a r.
  Typeable a =>
  Object ->
  (forall c f. ManagedColumn c f a => Object -> c a -> Edh r) ->
  Edh r
withColumnOf !obj !withCol = do
  let withComposition :: [Object] -> Edh r
      withComposition [] =
        naM $ "not expected Column of type: " <> T.pack (show $ typeRep @a)
      withComposition (o : rest) =
        (<|> withComposition rest) $
          asColumnOf @a o $ withCol o
  supers <- readTVarEdh $ edh'obj'supers obj
  withComposition $ obj : supers

withColumnOf' ::
  forall a r.
  Typeable a =>
  EdhValue ->
  (forall c f. ManagedColumn c f a => Object -> c a -> Edh r) ->
  Edh r
withColumnOf' !val !withCol = case edhUltimate val of
  EdhObject !obj -> withColumnOf obj withCol
  _ ->
    naM $ "not expected Column object of type: " <> T.pack (show $ typeRep @a)

withColumnSelfOf ::
  forall a r.
  Typeable a =>
  (forall c f. ManagedColumn c f a => Object -> c a -> Edh r) ->
  Edh r
withColumnSelfOf !withCol = mEdh $ \ !exit !ets -> do
  let that = edh'scope'that $ contextScope $ edh'context ets
  flip (runEdh ets) exit $ withColumnOf @a that withCol

getColumnDtype :: Object -> Edh Object
getColumnDtype !objCol = do
  let findSuperDto :: [Object] -> Edh Object
      findSuperDto [] =
        edhSimpleDescM (EdhObject objCol) >>= \ !badDesc ->
          naM $ "not a Column with dtype: " <> badDesc
      -- this is right and avoids unnecessary checks in vastly usual cases
      findSuperDto [dto] = return dto
      -- safe guard in case a Column instance has been further extended
      findSuperDto (maybeDto : rest) =
        (<|> findSuperDto rest) $
          withDataType maybeDto $ const $ return maybeDto
  readTVarEdh (edh'obj'supers objCol) >>= findSuperDto

sliceColumn ::
  Object ->
  SomeColumn ->
  Int ->
  Int ->
  Int ->
  EIO (Object, SomeColumn)
sliceColumn !objCol (SomeColumn _ !col) !start !stop !step =
  withSliced
    =<< if stop >= start && step == 1
      then view'column'slice col start stop
      else copy'column'slice col stop start stop step
  where
    withSliced (disp, col') = liftEdh $ case disp of
      StayComposed ->
        (,col') <$> mutCloneHostObjectM objCol objCol col'
      ExtractAlone -> do
        !dto <- getColumnDtype objCol
        let clsCol = edh'obj'class objCol
        (,col') <$> createHostObjectM' clsCol (toDyn col') [dto]

extractColumnBool ::
  forall c' f'.
  (ManagedColumn c' f' YesNo) =>
  Object ->
  SomeColumn ->
  c' YesNo ->
  EIO (Object, SomeColumn)
extractColumnBool !objCol (SomeColumn _ !col) !colMask = do
  !col' <- extract'column'bool col colMask
  liftEdh $ do
    !dto <- getColumnDtype objCol
    (,col') <$> createHostObjectM' clsCol (toDyn col') [dto]
  where
    clsCol = edh'obj'class objCol

extractColumnFancy ::
  forall c' f'.
  (ManagedColumn c' f' Int) =>
  Object ->
  SomeColumn ->
  c' Int ->
  EIO (Object, SomeColumn)
extractColumnFancy !objCol (SomeColumn _ !col) !colIdxs = do
  !col' <- extract'column'fancy col colIdxs
  liftEdh $ do
    !dto <- getColumnDtype objCol
    (,col') <$> createHostObjectM' clsCol (toDyn col') [dto]
  where
    clsCol = edh'obj'class objCol

idxAssignColumn :: SomeColumn -> EdhValue -> EdhValue -> Edh ()
idxAssignColumn (SomeColumn _ (col :: c0 a)) !idxVal !tgtVal =
  liftEIO (view'column'data col) >>= \(!cs, !cl) -> do
    let withScalarRHS :: Edh ()
        withScalarRHS =
          fromEdh @a tgtVal >>= \ !rhv -> do
            let byBoolIdx ::
                  forall c f.
                  ManagedColumn c f YesNo =>
                  Object ->
                  c YesNo ->
                  Edh ()
                byBoolIdx _ !idxCol = liftEIO $ do
                  (idxa, idxl) <- view'column'data idxCol
                  if idxl /= cl
                    then
                      throwEIO UsageError $
                        "bool index shape mismatch - "
                          <> T.pack (show idxl)
                          <> " vs "
                          <> T.pack (show cl)
                    else do
                      let go :: Int -> EIO ()
                          go i
                            | i >= idxl = return ()
                            | otherwise = do
                              YesNo yn <- liftIO $ array'reader idxa i
                              when (yn /= 0) $ liftIO $ array'writer cs i rhv
                              go (i + 1)
                      go 0

                byIntpIdx ::
                  forall c f.
                  ManagedColumn c f Int =>
                  Object ->
                  c Int ->
                  Edh ()
                byIntpIdx _ !idxCol = liftEIO $ do
                  (idxa, idxl) <- view'column'data idxCol
                  let go :: Int -> EIO ()
                      go i
                        | i >= idxl = return ()
                        | otherwise = do
                          idxi <- liftIO $ array'reader idxa i
                          liftIO $ array'writer cs idxi rhv
                          go (i + 1)
                  go 0

                byEdhIdx :: Edh ()
                byEdhIdx =
                  parseEdhIndexM idxVal >>= \case
                    Left !err -> throwEdhM UsageError err
                    Right !idx -> do
                      let fillAll :: IO ()
                          fillAll = go 0
                            where
                              go :: Int -> IO ()
                              go i
                                | i >= cl = return ()
                                | otherwise = do
                                  array'writer cs i rhv
                                  go (i + 1)
                      case idx of
                        EdhIndex !i -> liftIO $ array'writer cs i rhv
                        EdhAny -> liftIO fillAll
                        EdhAll -> liftIO fillAll
                        EdhSlice !start !stop !step ->
                          regulateEdhSliceM cl (start, stop, step)
                            >>= \(!iStart, !iStop, !iStep) -> liftIO $ do
                              let go :: Int -> IO ()
                                  go i
                                    | i >= iStop = return ()
                                    | otherwise = do
                                      array'writer cs i rhv
                                      go (i + iStep)
                              go iStart

            withColumnOf' @YesNo idxVal byBoolIdx
              <|> withColumnOf' @Int idxVal byIntpIdx
              <|> byEdhIdx

    (<|> withScalarRHS) $
      withColumnOf' @a tgtVal $ \_rhsColInst !rhsCol -> do
        (cs'rhs, cl'rhs) <- liftEIO $ view'column'data rhsCol
        let byBoolIdx ::
              forall c f.
              ManagedColumn c f YesNo =>
              Object ->
              c YesNo ->
              Edh ()
            byBoolIdx _ !idxCol =
              if cl'rhs /= cl
                then
                  throwEdhM UsageError $
                    "rhs column shape mismatch - "
                      <> T.pack (show cl'rhs)
                      <> " vs "
                      <> T.pack (show cl)
                else liftEIO $ do
                  (idxa, idxl) <- view'column'data idxCol
                  if idxl /= cl
                    then
                      throwEIO UsageError $
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
                      liftIO $ go 0

            byIntpIdx ::
              forall c f.
              ManagedColumn c f Int =>
              Object ->
              c Int ->
              Edh ()
            byIntpIdx _ !idxCol = liftEIO $ do
              (idxa, idxl) <- view'column'data idxCol
              if cl'rhs /= idxl
                then
                  throwEIO UsageError $
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
                  liftIO $ go 0

            byEdhIdx :: Edh ()
            byEdhIdx =
              parseEdhIndexM idxVal >>= \case
                Left !err -> throwEdhM UsageError err
                Right !idx -> case idx of
                  EdhIndex _i ->
                    throwEdhM
                      UsageError
                      "can not index-assign a rhs column by scalar index"
                  EdhAny ->
                    throwEdhM
                      UsageError
                      "can not index-assign a rhs column by Any index"
                  EdhAll ->
                    if cl'rhs /= cl
                      then
                        throwEdhM UsageError $
                          "rhs column shape mismatch - "
                            <> T.pack (show cl'rhs)
                            <> " vs "
                            <> T.pack (show cl)
                      else do
                        let go :: Int -> IO ()
                            go i
                              | i >= cl = return ()
                              | otherwise = do
                                array'reader cs'rhs i
                                  >>= array'writer cs i
                                go (i + 1)
                        liftIO $ go 0
                  EdhSlice !start !stop !step ->
                    regulateEdhSliceM cl (start, stop, step)
                      >>= \(!iStart, !iStop, !iStep) ->
                        if cl'rhs < ((iStop - iStart) `quot` iStep)
                          then
                            throwEdhM UsageError $
                              "rhs column shape mismatch slicing index - "
                                <> T.pack (show cl'rhs)
                                <> " vs "
                                <> T.pack
                                  ( show iStart <> ":" <> show iStop <> ":"
                                      <> show iStep
                                  )
                          else do
                            let go :: Int -> Int -> IO ()
                                go i n
                                  | i >= iStop = return ()
                                  | otherwise = do
                                    array'reader cs'rhs n
                                      >>= array'writer cs i
                                    go (i + iStep) (n + 1)
                            liftIO $ go iStart 0

        withColumnOf' @YesNo idxVal byBoolIdx
          <|> withColumnOf' @Int idxVal byIntpIdx
          <|> byEdhIdx

-- * Implementation details for pretty showing of column data

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

showColContent :: ArrayLength -> (ArrayIndex -> Edh Text) -> Edh Text
showColContent !cl !readElem = tryHeadLines [] 0 0 "" 0
  where
    -- todo make these tunable
    lineWidth = 79
    maxHeadLines = 10

    tryHeadLines ::
      [Line2Show] -> Int -> ArrayIndex -> Text2Show -> ArrayIndex -> Edh Text
    tryHeadLines cumLines nLines i line lineFirstElemIdx
      -- got all elements
      | i >= cl =
        if nLines <= 0
          then return $ TL.toStrict $ text'to'show line
          else do
            let cumLines' =
                  if text'len line > 0
                    then Line2Show line lineFirstElemIdx (cl - 1) : cumLines
                    else cumLines
                headLines = concat $ fancyLine <$> reverse cumLines'
            return $ TL.toStrict $ TL.unlines headLines

      -- more elements to show
      | nLines >= maxHeadLines = do
        showTailLines (reverse cumLines) (lineFirstElemIdx - 1)

      -- one more element to add
      | otherwise = do
        !elemTxt <- readElem i
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

    showTailLines :: [Line2Show] -> ArrayIndex -> Edh Text
    showTailLines hls headIdxShown = go [] 0 (cl - 1) "" (cl - 1)
      where
        go ::
          [Line2Show] ->
          Int ->
          ArrayIndex ->
          Text2Show ->
          ArrayIndex ->
          Edh Text
        go cumLines nLines i line lineLastElemIdx
          -- not that many elements, we can show its entirty
          | i <= headIdxShown = do
            let cumLines' = Line2Show line (i + 1) lineLastElemIdx : cumLines
                headLines = concat $ fancyLine <$> hls
                tailLines = concat $ fancyLine <$> cumLines'
            return $ TL.toStrict $ TL.unlines $ headLines ++ tailLines

          -- more elements then we'd show
          | nLines >= maxHeadLines = do
            let headLines = concat $ fancyLine <$> hls
                tailLines = concat $ fancyLine <$> cumLines
            return $
              TL.toStrict $ TL.unlines $ headLines ++ [" ... "] ++ tailLines

          -- one more element to add
          | otherwise = do
            !elemTxt <- readElem i
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
