
module Dim.Table where

import           Prelude
-- import           Debug.Trace

import           Unsafe.Coerce
import           GHC.Conc                       ( unsafeIOToSTM )

import           Foreign                 hiding ( void )

import           Control.Monad
import           Control.Monad.Reader

import           Control.Concurrent.STM

-- import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.HashMap.Strict           as Map
import           Data.Dynamic

import           Data.Vector.Storable           ( Vector )

import           Data.Lossless.Decimal         as D

import           Language.Edh.EHI

import           Dim.XCHG
import           Dim.DataType


-- | A column is a 1-dimensional array with pre-allocated storage capacity,
-- safely typed for data manipulation.
data Column where
  Column ::(Storable a, EdhXchg a) => {
      -- | convey type safe manipulation operations by an instance, making each
      -- column suitable to be wrapped within an untyped Edh object
      --
      -- this field of type `DataType a` without wrapped in a
      -- `ConcreteDataType`, coincides with `column'storage` sharing the
      -- identical type parameter `a` as for the ops to be type safe
      column'data'type :: !(DataType a)

      -- | dtype object, a bit redundant to above, but here to be directly
      -- obtained by Edh code from a Column object
    , column'dto :: !Object

      -- | column length is number of valid elements, can never be greater than
      -- storage vector's length
    , column'length :: !(TVar Int)

      -- | physical storage of the column data, length of the Vector should be
      -- considered capacity of the column
      --
      -- the underlying storage is mutable anytime, thread safety has to be
      -- guaranteed by proper mediation otherwise, e.g. content to set a
      -- changer attribute to a thread's identity before modifiying a column,
      -- and check such a attribute to be `frozen` valued before allowing the
      -- STM tx to commit
    , column'storage :: !(TVar (FlatArray a))
    } -> Column
 deriving Typeable

createColumn
  :: EdhProgState -> Object -> Int -> TVar Int -> (Column -> STM ()) -> STM ()
createColumn !pgs !dto !cap !clv !exit =
  fromDynamic <$> readTVar (entity'store $ objEntity dto) >>= \case
    Nothing ->
      throwEdhSTM pgs UsageError "Invalid dtype object to create a Column"
    Just (ConcreteDataType !dt) -> create'flat'array dt pgs cap
      $ \ !cs -> exit =<< Column dt dto clv <$> newTVar cs

columnCapacity :: Column -> STM Int
columnCapacity (Column _ _ _ !csv) = flatArrayCapacity <$> readTVar csv

columnLength :: Column -> STM Int
columnLength (Column _ _ !clv _) = readTVar clv

markColumnLength :: Column -> Int -> STM ()
markColumnLength (Column _ _ !clv _) !newLen = writeTVar clv newLen

readColumnCell
  :: EdhProgState -> Int -> Column -> (EdhValue -> STM ()) -> STM ()
readColumnCell !pgs !idx (Column !dt _ _ !csv) !exit =
  readTVar csv >>= \ !cs -> read'flat'array'cell dt pgs idx cs exit

writeColumnCell
  :: EdhProgState -> EdhValue -> Int -> Column -> (EdhValue -> STM ()) -> STM ()
writeColumnCell !pgs !val !idx (Column !dt _ _ !csv) !exit =
  readTVar csv >>= \ !cs -> write'flat'array'cell dt pgs val idx cs exit

fillColumn :: EdhProgState -> EdhValue -> [Int] -> Column -> STM () -> STM ()
fillColumn !pgs !val !idxs (Column !dt _ _ !csv) !exit =
  fromEdh pgs val $ \ !sv -> readTVar csv
    >>= \ !cs -> update'flat'array dt pgs [ (i, sv) | i <- idxs ] cs exit

growColumn :: EdhProgState -> Column -> Int -> STM () -> STM ()
growColumn !pgs (Column !dt _ !clv !csv) !newCap !exit =
  readTVar csv >>= \ !cs -> grow'flat'array dt pgs cs newCap $ \ !cs' -> do
    writeTVar csv cs'
    -- shink valid length if new capacity shrunk shorter than that
    !cl <- readTVar clv
    when (newCap < cl) $ writeTVar clv newCap
    -- done
    exit

vecCmpColumn
  :: EdhProgState
  -> Object
  -> (Ordering -> Bool)
  -> Column
  -> EdhValue
  -> (Column -> STM ())
  -> STM ()
vecCmpColumn !pgs !boolDTO !cmp (Column !dt _ !clv !csv) !v !exit =
  fromDynamic <$> readTVar (entity'store $ objEntity boolDTO) >>= \case
    Nothing ->
      throwEdhSTM pgs UsageError "Invalid dtype object to create a Column"
    Just (ConcreteDataType !bdt) -> do
      !cl <- readTVar clv
      !cs <- readTVar csv
      let !fa = unsafeSliceFlatArray cs 0 cl
      dt'cmp'vectorized dt pgs fa cmp v $ \ !bifa -> do
        !biclv <- newTVar cl
        !bicsv <- newTVar bifa
        exit $ Column (unsafeCoerce bdt) boolDTO biclv bicsv

elemCmpColumn
  :: EdhProgState
  -> Object
  -> (Ordering -> Bool)
  -> Column
  -> Column
  -> (Column -> STM ())
  -> STM ()
elemCmpColumn !pgs !boolDTO !cmp (Column !dt1 _ !clv1 !csv1) (Column !dt2 _ !clv2 !csv2) !exit
  = fromDynamic <$> readTVar (entity'store $ objEntity boolDTO) >>= \case
    Nothing ->
      throwEdhSTM pgs UsageError "Invalid dtype object to create a Column"
    Just (ConcreteDataType !bdt) ->
      if data'type'identifier dt1 /= data'type'identifier dt2
        then
          throwEdhSTM pgs UsageError
          $  "Column dtype mismatch: "
          <> data'type'identifier dt1
          <> " vs "
          <> data'type'identifier dt2
        else do
          !cl1 <- readTVar clv1
          !cl2 <- readTVar clv2
          if cl1 /= cl2
            then
              throwEdhSTM pgs UsageError
              $  "Column length mismatch: "
              <> T.pack (show cl1)
              <> " vs "
              <> T.pack (show cl2)
            else do
              !cs1 <- readTVar csv1
              !cs2 <- readTVar csv2
              let !fa1 = unsafeSliceFlatArray cs1 0 cl1
                  !fa2 = unsafeSliceFlatArray cs2 0 cl2
              dt'cmp'element'wise dt1 pgs fa1 cmp (unsafeCoerce fa2)
                $ \ !bifa -> do
                    !biclv <- newTVar cl1
                    !bicsv <- newTVar bifa
                    exit $ Column (unsafeCoerce bdt) boolDTO biclv bicsv


-- obtain valid column data as an immutable Storable Vector
-- this is unsafe in both memory/type regards and thread regard
unsafeCastColumnData
  :: forall a . (Storable a, EdhXchg a) => Column -> STM (Vector a)
unsafeCastColumnData (Column _ _ _ !csv) = do
  !ary <- readTVar csv
  return $ unsafeFlatArrayToVector ary


-- | host constructor Column(capacity, length=None, dtype=f8)
colCtor :: EdhValue -> EdhHostCtor
colCtor !defaultDataType !pgsCtor !apk !ctorExit =
  case parseArgsPack (Nothing, -1 :: Int, defaultDataType) ctorArgsParser apk of
    Left err -> throwEdhSTM pgsCtor UsageError err
    Right (Nothing, _, _) -> throwEdhSTM pgsCtor UsageError "Missing capacity"
    Right (Just !cap, !len, !dtv) -> case dtv of
      EdhObject !dto -> do
        lv <- newTVar $ if len < 0 then cap else len
        createColumn pgsCtor dto cap lv $ \ !col -> ctorExit $ toDyn col
      _ -> throwEdhSTM pgsCtor UsageError "Invalid dtype"
 where
  ctorArgsParser =
    ArgsPackParser
        [ \arg (_, len, dto) -> case arg of
          EdhDecimal !capVal -> case D.decimalToInteger capVal of
            Just !cap | cap >= 0 -> Right (Just $ fromInteger cap, len, dto)
            _ -> Left "Expect a positive interger for capacity"
          _ -> Left "Invalid capacity"
        , \arg (cap, _, dto) -> case arg of
          EdhDecimal !lenVal -> case D.decimalToInteger lenVal of
            Just !len | len >= 0 -> Right (cap, fromIntegral len, dto)
            _                    -> Left "Expect a positive interger for length"
          _ -> Left "Invalid length"
        , \arg (cap, len, _) -> case arg of
          dto@EdhObject{} -> Right (cap, len, dto)
          _               -> Left "Invalid dtype"
        ]
      $ Map.fromList
          [ ( "length"
            , \arg (cap, _, dto) -> case arg of
              EdhDecimal !lenVal -> case D.decimalToInteger lenVal of
                Just !len | len >= 0 -> Right (cap, fromInteger len, dto)
                _ -> Left "Expect a positive interger for length"
              _ -> Left "Invalid length"
            )
          , ( "dtype"
            , \arg (cap, len, _) -> case arg of
              dto@EdhObject{} -> Right (cap, len, dto)
              _               -> Left "Invalid dtype"
            )
          ]

colMethods :: Object -> Object -> EdhProgState -> STM [(AttrKey, EdhValue)]
-- CAVEAT: it's not checked but
--        *) 'indexDTO' must wrap `DataType Int`
--        *) 'boolDTO' must wrap `DataType VecBool`
colMethods !indexDTO !boolDTO !pgsModule =
  sequence
    $  [ (AttrByName nm, ) <$> mkHostProc scope vc nm hp mthArgs
       | (nm, vc, hp, mthArgs) <-
         [ ( "grow"
           , EdhMethod
           , colGrowProc
           , PackReceiver [mandatoryArg "newCapacity"]
           )
         , ("[]", EdhMethod, colIdxReadProc, PackReceiver [mandatoryArg "idx"])
         , ( "[=]"
           , EdhMethod
           , colIdxWriteProc
           , PackReceiver [mandatoryArg "idx", mandatoryArg "val"]
           )
         , ("__repr__", EdhMethod, colReprProc, PackReceiver [])
         , ( "=="
           , EdhMethod
           , colCmpProc $ \case
             EQ -> True
             _  -> False
           , PackReceiver [mandatoryArg "other"]
           )
         , ( "==@"
           , EdhMethod
           , colCmpProc $ \case
             EQ -> True
             _  -> False
           , PackReceiver [mandatoryArg "other"]
           )
         , ( ">="
           , EdhMethod
           , colCmpProc $ \case
             GT -> True
             EQ -> True
             _  -> False
           , PackReceiver [mandatoryArg "other"]
           )
         , ( "<="
           , EdhMethod
           , colCmpProc $ \case
             LT -> True
             EQ -> True
             _  -> False
           , PackReceiver [mandatoryArg "other"]
           )
         , ( "<"
           , EdhMethod
           , colCmpProc $ \case
             LT -> True
             _  -> False
           , PackReceiver [mandatoryArg "other"]
           )
         , ( ">"
           , EdhMethod
           , colCmpProc $ \case
             GT -> True
             _  -> False
           , PackReceiver [mandatoryArg "other"]
           )
         , ( ">=@"
           , EdhMethod
           , colCmpProc $ \case
             LT -> True
             EQ -> True
             _  -> False
           , PackReceiver [mandatoryArg "other"]
           )
         , ( "<=@"
           , EdhMethod
           , colCmpProc $ \case
             GT -> True
             EQ -> True
             _  -> False
           , PackReceiver [mandatoryArg "other"]
           )
         , ( "<@"
           , EdhMethod
           , colCmpProc $ \case
             GT -> True
             _  -> False
           , PackReceiver [mandatoryArg "other"]
           )
         , ( ">@"
           , EdhMethod
           , colCmpProc $ \case
             LT -> True
             _  -> False
           , PackReceiver [mandatoryArg "other"]
           )
         ]
       ]
    ++ [ (AttrByName nm, ) <$> mkHostProperty scope nm getter setter
       | (nm, getter, setter) <-
         [ ("capacity", colCapProc  , Nothing)
         , ("length"  , colLenProc  , Just colMarkLenProc)
         , ("dtype"   , colDtypeProc, Nothing)
         ]
       ]
 where
  !scope = contextScope $ edh'context pgsModule

  colGrowProc :: EdhProcedure
  colGrowProc (ArgsPack [EdhDecimal !newCapNum] !kwargs) !exit
    | Map.null kwargs = case D.decimalToInteger newCapNum of
      Just !newCap | newCap >= 0 -> withThatEntity $ \ !pgs !col ->
        growColumn pgs col (fromInteger newCap)
          $ exitEdhSTM pgs exit
          $ EdhObject
          $ thatObject
          $ contextScope
          $ edh'context pgs
      _ -> throwEdh UsageError "Column capacity must be a positive integer"
  colGrowProc _ _ = throwEdh UsageError "Invalid args to Column.grow()"

  colIdxReadProc :: EdhProcedure
  colIdxReadProc (ArgsPack !args _) !exit = withThatEntity $ \ !pgs !col ->
    case args of
      -- TODO support slice indexing and @indexDataType@ typed fancy indexing
      [EdhDecimal !idxNum] -> case D.decimalToInteger idxNum of
        Just !idx ->
          readColumnCell pgs (fromInteger idx) col $ exitEdhSTM pgs exit
        _ ->
          throwEdhSTM pgs UsageError
            $  "Expect an integer to index a Column but you give: "
            <> T.pack (show idxNum)
      _ ->
        throwEdhSTM pgs UsageError $ "Invalid index for a Column: " <> T.pack
          (show args)

  colIdxWriteProc :: EdhProcedure
  colIdxWriteProc (ArgsPack !args _) !exit = withThatEntity $ \ !pgs !col ->
    case args of
      -- TODO support slice indexing and @indexDataType@ typed fancy indexing
      [EdhDecimal !idxNum, val] -> case D.decimalToInteger idxNum of
        Just !idx ->
          writeColumnCell pgs val (fromInteger idx) col $ exitEdhSTM pgs exit
        _ ->
          throwEdhSTM pgs UsageError
            $  "Expect an integer to index a Column but you give: "
            <> T.pack (show idxNum)
      _ ->
        throwEdhSTM pgs UsageError $ "Invalid index for a Column: " <> T.pack
          (show args)

  colCapProc :: EdhProcedure
  colCapProc _ !exit = withThatEntity $ \ !pgs !col -> columnCapacity col
    >>= \ !cap -> exitEdhSTM pgs exit $ EdhDecimal $ fromIntegral cap

  colLenProc :: EdhProcedure
  colLenProc _ !exit = withThatEntity $ \ !pgs !col -> columnLength col
    >>= \ !len -> exitEdhSTM pgs exit $ EdhDecimal $ fromIntegral len

  colMarkLenProc :: EdhProcedure
  colMarkLenProc (ArgsPack [EdhDecimal !newLenNum] !kwargs) !exit
    | Map.null kwargs = withThatEntity $ \ !pgs !col -> do
      !cap <- columnCapacity col
      case D.decimalToInteger newLenNum of
        Just !newLen | newLen >= 0 && newLen <= fromIntegral cap ->
          markColumnLength col (fromInteger newLen) >> exitEdhSTM pgs exit nil
        _ -> throwEdhSTM pgs UsageError "Column length out of range"
  colMarkLenProc _ _ =
    throwEdh UsageError "Invalid args to Column.markLength()"

  colDtypeProc :: EdhProcedure
  colDtypeProc _ !exit = withThatEntity
    $ \ !pgs (Column _ !dto _ _) -> exitEdhSTM pgs exit $ EdhObject dto

  colReprProc :: EdhProcedure
  colReprProc _ !exit = withThatEntity $ \ !pgs (Column _ !dto !clv !csv) ->
    fromDynamic <$> readTVar (entity'store $ objEntity dto) >>= \case
      Nothing                     -> error "bug: bad dto"
      Just (ConcreteDataType !dt) -> do
        !cl <- readTVar clv
        !cs <- readTVar csv
        exitEdhSTM pgs exit
          $  EdhString
          $  "Column("
          <> T.pack (show $ flatArrayCapacity cs)
          <> ", length="
          <> T.pack (show cl)
          <> ", dtype="
          <> data'type'identifier dt
          <> ")"

  colCmpProc :: (Ordering -> Bool) -> EdhProcedure
  colCmpProc !cmp (ArgsPack [!other] _) !exit =
    withThatEntity $ \ !pgs !col -> case edhUltimate other of
      otherVal@(EdhObject !otherObj) ->
        fromDynamic <$> objStore otherObj >>= \case
          Just colOther@Column{} ->
            elemCmpColumn pgs boolDTO cmp col colOther $ \ !colResult ->
              cloneEdhObject (thatObject $ contextScope $ edh'context pgs)
                             (\_ !esdx -> esdx $ toDyn colResult)
                $ \ !bio -> exitEdhSTM pgs exit $ EdhObject bio
          Nothing ->
            vecCmpColumn pgs boolDTO cmp col otherVal $ \ !colResult ->
              cloneEdhObject (thatObject $ contextScope $ edh'context pgs)
                             (\_ !esdx -> esdx $ toDyn colResult)
                $ \ !bio -> exitEdhSTM pgs exit $ EdhObject bio
      !otherVal -> vecCmpColumn pgs boolDTO cmp col otherVal $ \ !colResult ->
        cloneEdhObject (thatObject $ contextScope $ edh'context pgs)
                       (\_ !esdx -> esdx $ toDyn colResult)
          $ \ !bio -> exitEdhSTM pgs exit $ EdhObject bio
  colCmpProc _ !apk _ =
    throwEdh UsageError $ "Invalid args for a Column operator: " <> T.pack
      (show apk)


arangeProc :: Object -> EntityManipulater -> Class -> EdhProcedure
arangeProc !indexDTO !emColumn !clsColumn (ArgsPack [rngSpec] _) !exit =
  case rngSpec of
    EdhPair (EdhPair (EdhDecimal !startN) (EdhDecimal !stopN)) (EdhDecimal stepN)
      -> case D.decimalToInteger startN of
        Just !start -> case D.decimalToInteger stopN of
          Just !stop -> case D.decimalToInteger stepN of
            Just !step -> createRangeCol (fromInteger start)
                                         (fromInteger stop)
                                         (fromInteger step)
            _ -> throwEdh UsageError "step is not an integer"
          _ -> throwEdh UsageError "stop is not an integer"
        _ -> throwEdh UsageError "start is not an integer"
    EdhPair (EdhDecimal !startN) (EdhDecimal !stopN) ->
      case D.decimalToInteger startN of
        Just !start -> case D.decimalToInteger stopN of
          Just !stop ->
            createRangeCol (fromInteger start) (fromInteger stop)
              $ if stop >= start then 1 else -1
          _ -> throwEdh UsageError "stop is not an integer"
        _ -> throwEdh UsageError "start is not an integer"
    EdhDecimal !stopN -> case D.decimalToInteger stopN of
      Just !stop ->
        createRangeCol 0 (fromInteger stop) $ if stop >= 0 then 1 else -1
      _ -> throwEdh UsageError "stop is not an integer"
    _ -> throwEdh UsageError $ "Invalid range of " <> T.pack
      (edhTypeNameOf rngSpec)
 where
  exitWithNewColObj !pgs !col = do
    !ent    <- createSideEntity emColumn $ toDyn col
    !colObj <- viewAsEdhObject ent clsColumn []
    exitEdhSTM pgs exit $ EdhObject colObj
  createRangeCol :: Int -> Int -> Int -> EdhProc
  createRangeCol !start !stop !step = ask >>= \ !pgs ->
    contEdhSTM $ if stop == start
      then do
        !clv <- newTVar 0
        createColumn pgs indexDTO 0 clv $ \ !col -> exitWithNewColObj pgs col
      else if (stop > start && step <= 0) || (stop < start && step >= 0)
        then throwEdhSTM pgs UsageError "Range is not converging"
        else do
          let (q, r) = quotRem (stop - start) step
              !len   = if r == 0 then abs q else 1 + abs q
              fillRng :: Ptr Int -> Int -> Int -> IO ()
              fillRng !p !n !i = if i >= len
                then return ()
                else do
                  pokeElemOff p i n
                  fillRng p (n + step) (i + 1)
          !clv <- newTVar len
          createColumn pgs indexDTO len clv $ \col@(Column _ _ _ !csv) -> do
            (FlatArray _ !fp) <- unsafeCoerce <$> readTVar csv
            void $ unsafeIOToSTM $ withForeignPtr fp $ \ !p -> fillRng p start 0
            exitWithNewColObj pgs col
arangeProc _ _ _ _ _ = throwEdh UsageError "Invalid args to arange()"

