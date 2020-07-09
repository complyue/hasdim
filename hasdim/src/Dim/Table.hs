
module Dim.Table where

import           Prelude
-- import           Debug.Trace

import           Unsafe.Coerce
-- import           GHC.Conc                       ( unsafeIOToSTM )

import           Foreign                 hiding ( void )

import           Control.Monad
import           Control.Monad.Reader

import           Control.Concurrent.STM

import           Data.Text                      ( Text )
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

vecOpColumn
  :: EdhProgState
  -> (Text -> Dynamic)
  -> Column
  -> EdhValue
  -> STM ()
  -> (Column -> STM ())
  -> STM ()
vecOpColumn !pgs !getOp (Column !dt !dto !clv !csv) !v !naExit !exit = do
  let !dop = getOp $ data'type'identifier dt
  case fromDynamic dop of
    Just EdhNil -> naExit
    _           -> do
      !cl <- readTVar clv
      !cs <- readTVar csv
      let !fa = unsafeSliceFlatArray cs 0 cl
      dt'op'vectorized dt pgs fa dop v $ \ !bifa -> do
        !biclv <- newTVar cl
        !bicsv <- newTVar bifa
        exit $ Column dt dto biclv bicsv

elemOpColumn
  :: EdhProgState
  -> (Text -> Dynamic)
  -> Column
  -> Column
  -> STM ()
  -> (Column -> STM ())
  -> STM ()
elemOpColumn !pgs !getOp (Column !dt1 !dto1 !clv1 !csv1) (Column !dt2 _dto2 !clv2 !csv2) !naExit !exit
  = let !dop = getOp $ data'type'identifier dt1
    in
      case fromDynamic dop of
        Just EdhNil -> naExit
        _           -> if data'type'identifier dt1 /= data'type'identifier dt2
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
                dt'op'element'wise dt1
                                   pgs
                                   fa1
                                   (getOp $ data'type'identifier dt1)
                                   (unsafeCoerce fa2)
                  $ \ !bifa -> do
                      !biclv <- newTVar cl1
                      !bicsv <- newTVar bifa
                      exit $ Column dt1 dto1 biclv bicsv

vecInpColumn
  :: EdhProgState
  -> (Text -> Dynamic)
  -> Column
  -> EdhValue
  -> STM ()
  -> STM ()
  -> STM ()
vecInpColumn !pgs !getOp (Column !dt _ !clv !csv) !v !naExit !exit = do
  let !dop = getOp $ data'type'identifier dt
  case fromDynamic dop of
    Just EdhNil -> naExit
    _           -> do
      !cl <- readTVar clv
      !cs <- readTVar csv
      let !fa = unsafeSliceFlatArray cs 0 cl
      dt'inp'vectorized dt pgs fa dop v exit

vecInpMaskedColumn
  :: EdhProgState
  -> Column
  -> (Text -> Dynamic)
  -> Column
  -> EdhValue
  -> STM ()
  -> STM ()
  -> STM ()
vecInpMaskedColumn !pgs (Column _ _ !mclv !mcsv) !getOp (Column !dt _ !clv !csv) !v !naExit !exit
  = do
    let !dop = getOp $ data'type'identifier dt
    case fromDynamic dop of
      Just EdhNil -> naExit
      _           -> do
        !mcl <- readTVar mclv
        !cl  <- readTVar clv
        if mcl /= cl
          then
            throwEdhSTM pgs UsageError
            $  "Index length mismatch: "
            <> T.pack (show mcl)
            <> " vs "
            <> T.pack (show cl)
          else do
            !mcs <- readTVar mcsv
            !cs  <- readTVar csv
            let !ma = unsafeSliceFlatArray mcs 0 mcl
                !fa = unsafeSliceFlatArray cs 0 cl
            dt'inp'vectorized'masked dt pgs (unsafeCoerce ma) fa dop v exit

elemInpColumn
  :: EdhProgState
  -> (Text -> Dynamic)
  -> Column
  -> Column
  -> STM ()
  -> STM ()
  -> STM ()
elemInpColumn !pgs !getOp (Column !dt1 _dto1 !clv1 !csv1) (Column !dt2 _dto2 !clv2 !csv2) !naExit !exit
  = let !dop = getOp $ data'type'identifier dt1
    in
      case fromDynamic dop of
        Just EdhNil -> naExit
        _           -> if data'type'identifier dt1 /= data'type'identifier dt2
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
                dt'inp'element'wise dt1
                                    pgs
                                    fa1
                                    (getOp $ data'type'identifier dt1)
                                    (unsafeCoerce fa2)
                                    exit

elemInpMaskedColumn
  :: EdhProgState
  -> Column
  -> (Text -> Dynamic)
  -> Column
  -> Column
  -> STM ()
  -> STM ()
  -> STM ()
elemInpMaskedColumn !pgs (Column _ _ !mclv !mcsv) !getOp (Column !dt1 _dto1 !clv1 !csv1) (Column !dt2 _dto2 !clv2 !csv2) !naExit !exit
  = let !dop = getOp $ data'type'identifier dt1
    in
      case fromDynamic dop of
        Just EdhNil -> naExit
        _           -> if data'type'identifier dt1 /= data'type'identifier dt2
          then
            throwEdhSTM pgs UsageError
            $  "Column dtype mismatch: "
            <> data'type'identifier dt1
            <> " vs "
            <> data'type'identifier dt2
          else do
            !mcl <- readTVar mclv
            !cl1 <- readTVar clv1
            !cl2 <- readTVar clv2
            if mcl /= cl1
              then
                throwEdhSTM pgs UsageError
                $  "Index length mismatch: "
                <> T.pack (show mcl)
                <> " vs "
                <> T.pack (show cl1)
              else if cl1 /= cl2
                then
                  throwEdhSTM pgs UsageError
                  $  "Column length mismatch: "
                  <> T.pack (show cl1)
                  <> " vs "
                  <> T.pack (show cl2)
                else do
                  !mcs <- readTVar mcsv
                  !cs1 <- readTVar csv1
                  !cs2 <- readTVar csv2
                  let !ma  = unsafeSliceFlatArray mcs 0 mcl
                      !fa1 = unsafeSliceFlatArray cs1 0 cl1
                      !fa2 = unsafeSliceFlatArray cs2 0 cl2
                  dt'inp'element'wise'masked
                    dt1
                    pgs
                    (unsafeCoerce ma)
                    fa1
                    (getOp $ data'type'identifier dt1)
                    (unsafeCoerce fa2)
                    exit


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
    Left !err -> throwEdhSTM pgsCtor UsageError err
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
         , ("__show__", EdhMethod, colShowProc, PackReceiver [])
         , ("__desc__", EdhMethod, colDescProc, PackReceiver [])
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
         , ( "!="
           , EdhMethod
           , colCmpProc $ \case
             EQ -> False
             _  -> True
           , PackReceiver [mandatoryArg "other"]
           )
         , ( "!=@"
           , EdhMethod
           , colCmpProc $ \case
             EQ -> False
             _  -> True
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
         , ( "&&"
           , EdhMethod
           , colOpProc bitAndOp
           , PackReceiver [mandatoryArg "other"]
           )
         , ( "&&@"
           , EdhMethod
           , colOpProc bitAndOp
           , PackReceiver [mandatoryArg "other"]
           )
         , ( "||"
           , EdhMethod
           , colOpProc bitOrOp
           , PackReceiver [mandatoryArg "other"]
           )
         , ( "||@"
           , EdhMethod
           , colOpProc bitOrOp
           , PackReceiver [mandatoryArg "other"]
           )
         , ( "&&="
           , EdhMethod
           , colInpProc bitAndOp
           , PackReceiver [mandatoryArg "other"]
           )
         , ( "||="
           , EdhMethod
           , colInpProc bitOrOp
           , PackReceiver [mandatoryArg "other"]
           )
         , ("+", EdhMethod, colOpProc addOp, PackReceiver [mandatoryArg "other"])
         , ( "+@"
           , EdhMethod
           , colOpProc addOp
           , PackReceiver [mandatoryArg "other"]
           )
         , ( "+="
           , EdhMethod
           , colInpProc addOp
           , PackReceiver [mandatoryArg "other"]
           )
         , ( "-"
           , EdhMethod
           , colOpProc subtractOp
           , PackReceiver [mandatoryArg "other"]
           )
         , ( "-@"
           , EdhMethod
           , colOpProc subtFromOp
           , PackReceiver [mandatoryArg "other"]
           )
         , ( "-="
           , EdhMethod
           , colInpProc subtractOp
           , PackReceiver [mandatoryArg "other"]
           )
         , ("*", EdhMethod, colOpProc mulOp, PackReceiver [mandatoryArg "other"])
         , ( "*@"
           , EdhMethod
           , colOpProc mulOp
           , PackReceiver [mandatoryArg "other"]
           )
         , ( "*="
           , EdhMethod
           , colInpProc mulOp
           , PackReceiver [mandatoryArg "other"]
           )
         , ("/", EdhMethod, colOpProc divOp, PackReceiver [mandatoryArg "other"])
         , ( "/@"
           , EdhMethod
           , colOpProc divByOp
           , PackReceiver [mandatoryArg "other"]
           )
         , ( "/="
           , EdhMethod
           , colInpProc divOp
           , PackReceiver [mandatoryArg "other"]
           )
         , ( "//"
           , EdhMethod
           , colOpProc divIntOp
           , PackReceiver [mandatoryArg "other"]
           )
         , ( "//@"
           , EdhMethod
           , colOpProc divIntByOp
           , PackReceiver [mandatoryArg "other"]
           )
         , ( "//="
           , EdhMethod
           , colInpProc divIntOp
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

  colShowProc :: EdhProcedure
  colShowProc _ !exit = withThatEntity $ \ !pgs (Column _ !dto !clv !csv) ->
    fromDynamic <$> readTVar (entity'store $ objEntity dto) >>= \case
      Nothing                     -> error "bug: bad dto"
      Just (ConcreteDataType !dt) -> do
        !cl <- readTVar clv
        !cs <- readTVar csv
        showData pgs dt cl (unsafeCoerce cs) 0 [] 0 ""
   where
    showData
      :: forall a
       . EdhProgState
      -> DataType a
      -> Int
      -> FlatArray a
      -> Int
      -> [Text]
      -> Int
      -> Text
      -> STM ()
    showData !pgs !dt !len !fa !i !cumLines !lineIdx !line = if i >= len
      then exitEdhSTM pgs exit $ EdhString
        (if T.null line && null cumLines
          then "Zero-Length Column"
          else if null cumLines
            then line
            else
              let !fullLines =
                    line
                      :  " # " -- todo make this tunable ?
                      <> T.pack (show lineIdx)
                      <> " ~ "
                      <> T.pack (show $ i - 1)
                      :  cumLines
                  !lineCnt = length fullLines
              in  if lineCnt > 20
                    then
                      T.unlines
                      $  reverse
                      $  take 10 fullLines
                      ++ ["# ... "] -- todo make this tunable
                      ++ drop (lineCnt - 10) fullLines
                    else T.unlines $ reverse fullLines
        )
      else read'flat'array'cell dt pgs i fa $ \ !elemVal ->
        edhValueReprSTM pgs elemVal $ \ !elemRepr ->
          let !tentLine = line <> elemRepr <> ", "
          in  if T.length tentLine > 79 -- todo make this tunable ?
                then showData
                  pgs
                  dt
                  len
                  fa
                  (i + 1)
                  ( line
                  : (  " # " -- todo make this tunable ?
                    <> T.pack (show lineIdx)
                    <> " ~ "
                    <> T.pack (show $ i - 1)
                    )
                  : cumLines
                  )
                  i
                  (elemRepr <> ", ")
                else showData pgs dt len fa (i + 1) cumLines lineIdx tentLine

  -- TODO impl. this following:
  --      https://pandas.pydata.org/pandas-docs/stable/reference/api/pandas.Series.describe.html
  colDescProc :: EdhProcedure
  colDescProc _ !exit =
    exitEdhProc exit
      $  EdhString
      $  " * Statistical Description of Column data,\n"
      <> "   like pandas describe(), is yet to be implemented."


  colIdxReadProc :: EdhProcedure
  colIdxReadProc (ArgsPack !args _) !exit = withThatEntity $ \ !pgs !col ->
    case args of
      [EdhDecimal !idxNum] -> case D.decimalToInteger idxNum of
        Just !idx ->
          readColumnCell pgs (fromInteger idx) col $ exitEdhSTM pgs exit
        _ ->
          throwEdhSTM pgs UsageError
            $  "Expect an integer to index a Column but you give: "
            <> T.pack (show idxNum)
      -- TODO support slice indexing and @indexDataType@ typed fancy indexing
      _ ->
        throwEdhSTM pgs UsageError $ "Invalid index for a Column: " <> T.pack
          (show args)

  colIdxWriteProc :: EdhProcedure
  colIdxWriteProc (ArgsPack !args _) !exit = withThatEntity $ \ !pgs !col ->
    let
      that = thatObject $ contextScope $ edh'context pgs
      assignAll !other = case edhUltimate other of
        otherVal@(EdhObject !otherObj) ->
          fromDynamic <$> objStore otherObj >>= \case
            Just colOther@Column{} ->
              elemInpColumn pgs
                            assignOp
                            col
                            colOther
                            (exitEdhSTM pgs exit EdhContinue)
                $ exitEdhSTM pgs exit
                $ EdhObject that
            Nothing ->
              vecInpColumn pgs
                           assignOp
                           col
                           otherVal
                           (exitEdhSTM pgs exit EdhContinue)
                $ exitEdhSTM pgs exit
                $ EdhObject that
        !otherVal ->
          vecInpColumn pgs
                       assignOp
                       col
                       otherVal
                       (exitEdhSTM pgs exit EdhContinue)
            $ exitEdhSTM pgs exit
            $ EdhObject that
    in
      case args of
        [EdhDecimal !idxNum, !val] -> case D.decimalToInteger idxNum of
          Just !idx ->
            writeColumnCell pgs val (fromInteger idx) col $ exitEdhSTM pgs exit
          _ ->
            throwEdhSTM pgs UsageError
              $  "Expect an integer to index a Column but you give: "
              <> T.pack (show idxNum)
        [EdhNamedValue "All" _, !other] -> assignAll other
        [EdhNamedValue "Any" _, !other] -> assignAll other
        [EdhArgsPack (ArgsPack [] !kwargs), !other] | Map.null kwargs ->
          assignAll other
        [EdhObject !idxObj, !other] ->
          fromDynamic <$> objStore idxObj >>= \case
            Just icol@(Column !idt _ _ _) -> case data'type'identifier idt of
              "bool" -> case edhUltimate other of
                -- bool index 
                otherVal@(EdhObject !otherObj) ->
                  fromDynamic <$> objStore otherObj >>= \case
                    Just colOther@Column{} ->
                      elemInpMaskedColumn pgs
                                          icol
                                          assignOp
                                          col
                                          colOther
                                          (exitEdhSTM pgs exit EdhContinue)
                        $ exitEdhSTM pgs exit
                        $ EdhObject that
                    Nothing ->
                      vecInpMaskedColumn pgs
                                         icol
                                         assignOp
                                         col
                                         otherVal
                                         (exitEdhSTM pgs exit EdhContinue)
                        $ exitEdhSTM pgs exit
                        $ EdhObject that
                !otherVal ->
                  vecInpMaskedColumn pgs
                                     icol
                                     assignOp
                                     col
                                     otherVal
                                     (exitEdhSTM pgs exit EdhContinue)
                    $ exitEdhSTM pgs exit
                    $ EdhObject that
              "intp" -> -- fancy index
                undefined -- TODO impl. this
              !badIdxDti ->
                throwEdhSTM pgs UsageError
                  $  "Invalid dtype as index for a Column: "
                  <> badIdxDti
            Nothing -> edhValueReprSTM pgs (EdhObject idxObj) $ \ !objRepr ->
              throwEdhSTM pgs UsageError
                $  "Invalid object as index for a Column: "
                <> objRepr
        -- TODO support slice indexing and @indexDataType@ typed fancy indexing
        _ ->
          throwEdhSTM pgs UsageError
            $  "Invalid args to assign a Column by index: "
            <> T.pack (show args)


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

  colOpProc :: (Text -> Dynamic) -> EdhProcedure
  colOpProc !getOp (ArgsPack [!other] _) !exit =
    withThatEntity $ \ !pgs !col -> case edhUltimate other of
      otherVal@(EdhObject !otherObj) ->
        fromDynamic <$> objStore otherObj >>= \case
          Just colOther@Column{} ->
            elemOpColumn pgs
                         getOp
                         col
                         colOther
                         (exitEdhSTM pgs exit EdhContinue)
              $ \ !colResult ->
                  cloneEdhObject (thatObject $ contextScope $ edh'context pgs)
                                 (\_ !esdx -> esdx $ toDyn colResult)
                    $ \ !bio -> exitEdhSTM pgs exit $ EdhObject bio
          Nothing ->
            vecOpColumn pgs getOp col otherVal (exitEdhSTM pgs exit EdhContinue)
              $ \ !colResult ->
                  cloneEdhObject (thatObject $ contextScope $ edh'context pgs)
                                 (\_ !esdx -> esdx $ toDyn colResult)
                    $ \ !bio -> exitEdhSTM pgs exit $ EdhObject bio
      !otherVal ->
        vecOpColumn pgs getOp col otherVal (exitEdhSTM pgs exit EdhContinue)
          $ \ !colResult ->
              cloneEdhObject (thatObject $ contextScope $ edh'context pgs)
                             (\_ !esdx -> esdx $ toDyn colResult)
                $ \ !bio -> exitEdhSTM pgs exit $ EdhObject bio
  colOpProc _ !apk _ =
    throwEdh UsageError $ "Invalid args for a Column operator: " <> T.pack
      (show apk)

  colInpProc :: (Text -> Dynamic) -> EdhProcedure
  colInpProc !getOp (ArgsPack [!other] _) !exit =
    withThatEntity $ \ !pgs !col ->
      let that = thatObject $ contextScope $ edh'context pgs
      in
        case edhUltimate other of
          otherVal@(EdhObject !otherObj) ->
            fromDynamic <$> objStore otherObj >>= \case
              Just colOther@Column{} ->
                elemInpColumn pgs
                              getOp
                              col
                              colOther
                              (exitEdhSTM pgs exit EdhContinue)
                  $ exitEdhSTM pgs exit
                  $ EdhObject that
              Nothing ->
                vecInpColumn pgs
                             getOp
                             col
                             otherVal
                             (exitEdhSTM pgs exit EdhContinue)
                  $ exitEdhSTM pgs exit
                  $ EdhObject that
          !otherVal ->
            vecInpColumn pgs
                         getOp
                         col
                         otherVal
                         (exitEdhSTM pgs exit EdhContinue)
              $ exitEdhSTM pgs exit
              $ EdhObject that
  colInpProc _ !apk _ =
    throwEdh UsageError $ "Invalid args for a Column operator: " <> T.pack
      (show apk)

  assignOp :: Text -> Dynamic
  assignOp = \case
    "float64" -> toDyn ((\_x !y -> y) :: Double -> Double -> Double)
    "float32" -> toDyn ((\_x !y -> y) :: Float -> Float -> Float)
    "int64"   -> toDyn ((\_x !y -> y) :: Int64 -> Int64 -> Int64)
    "int32"   -> toDyn ((\_x !y -> y) :: Int32 -> Int32 -> Int32)
    "int8"    -> toDyn ((\_x !y -> y) :: Int8 -> Int8 -> Int8)
    "byte"    -> toDyn ((\_x !y -> y) :: Word8 -> Word8 -> Word8)
    "intp"    -> toDyn ((\_x !y -> y) :: Int -> Int -> Int)
    "bool"    -> toDyn ((\_x !y -> y) :: VecBool -> VecBool -> VecBool)
    _         -> toDyn nil -- means not applicable here

  bitAndOp :: Text -> Dynamic
  bitAndOp = \case
    -- "float64" -> toDyn ((.&.) :: Double -> Double -> Double)
    -- "float32" -> toDyn ((.&.) :: Float -> Float -> Float)
    "int64" -> toDyn ((.&.) :: Int64 -> Int64 -> Int64)
    "int32" -> toDyn ((.&.) :: Int32 -> Int32 -> Int32)
    "int8"  -> toDyn ((.&.) :: Int8 -> Int8 -> Int8)
    "byte"  -> toDyn ((.&.) :: Word8 -> Word8 -> Word8)
    "intp"  -> toDyn ((.&.) :: Int -> Int -> Int)
    "bool"  -> toDyn ((.&.) :: VecBool -> VecBool -> VecBool)
    _       -> toDyn nil -- means not applicable here
  bitOrOp :: Text -> Dynamic
  bitOrOp = \case
    -- "float64" -> toDyn ((.|.) :: Double -> Double -> Double)
    -- "float32" -> toDyn ((.|.) :: Float -> Float -> Float)
    "int64" -> toDyn ((.|.) :: Int64 -> Int64 -> Int64)
    "int32" -> toDyn ((.|.) :: Int32 -> Int32 -> Int32)
    "int8"  -> toDyn ((.|.) :: Int8 -> Int8 -> Int8)
    "byte"  -> toDyn ((.|.) :: Word8 -> Word8 -> Word8)
    "intp"  -> toDyn ((.|.) :: Int -> Int -> Int)
    "bool"  -> toDyn ((.|.) :: VecBool -> VecBool -> VecBool)
    _       -> toDyn nil -- means not applicable here

  addOp :: Text -> Dynamic
  addOp = \case
    "float64" -> toDyn ((+) :: Double -> Double -> Double)
    "float32" -> toDyn ((+) :: Float -> Float -> Float)
    "int64"   -> toDyn ((+) :: Int64 -> Int64 -> Int64)
    "int32"   -> toDyn ((+) :: Int32 -> Int32 -> Int32)
    "int8"    -> toDyn ((+) :: Int8 -> Int8 -> Int8)
    "byte"    -> toDyn ((+) :: Word8 -> Word8 -> Word8)
    "intp"    -> toDyn ((+) :: Int -> Int -> Int)
    _         -> toDyn nil -- means not applicable here
  subtractOp :: Text -> Dynamic
  subtractOp = \case
    "float64" -> toDyn ((-) :: Double -> Double -> Double)
    "float32" -> toDyn ((-) :: Float -> Float -> Float)
    "int64"   -> toDyn ((-) :: Int64 -> Int64 -> Int64)
    "int32"   -> toDyn ((-) :: Int32 -> Int32 -> Int32)
    "int8"    -> toDyn ((-) :: Int8 -> Int8 -> Int8)
    "byte"    -> toDyn ((-) :: Word8 -> Word8 -> Word8)
    "intp"    -> toDyn ((-) :: Int -> Int -> Int)
    _         -> toDyn nil -- means not applicable here
  subtFromOp :: Text -> Dynamic
  subtFromOp = \case
    "float64" -> toDyn ((\ !x !y -> y - x) :: Double -> Double -> Double)
    "float32" -> toDyn ((\ !x !y -> y - x) :: Float -> Float -> Float)
    "int64"   -> toDyn ((\ !x !y -> y - x) :: Int64 -> Int64 -> Int64)
    "int32"   -> toDyn ((\ !x !y -> y - x) :: Int32 -> Int32 -> Int32)
    "int8"    -> toDyn ((\ !x !y -> y - x) :: Int8 -> Int8 -> Int8)
    "byte"    -> toDyn ((\ !x !y -> y - x) :: Word8 -> Word8 -> Word8)
    "intp"    -> toDyn ((\ !x !y -> y - x) :: Int -> Int -> Int)
    _         -> toDyn nil -- means not applicable here
  mulOp :: Text -> Dynamic
  mulOp = \case
    "float64" -> toDyn ((*) :: Double -> Double -> Double)
    "float32" -> toDyn ((*) :: Float -> Float -> Float)
    "int64"   -> toDyn ((*) :: Int64 -> Int64 -> Int64)
    "int32"   -> toDyn ((*) :: Int32 -> Int32 -> Int32)
    "int8"    -> toDyn ((*) :: Int8 -> Int8 -> Int8)
    "byte"    -> toDyn ((*) :: Word8 -> Word8 -> Word8)
    "intp"    -> toDyn ((*) :: Int -> Int -> Int)
    _         -> toDyn nil -- means not applicable here
  divOp :: Text -> Dynamic
  divOp = \case
    "float64" -> toDyn ((/) :: Double -> Double -> Double)
    "float32" -> toDyn ((/) :: Float -> Float -> Float)
    "int64"   -> toDyn (div :: Int64 -> Int64 -> Int64)
    "int32"   -> toDyn (div :: Int32 -> Int32 -> Int32)
    "int8"    -> toDyn (div :: Int8 -> Int8 -> Int8)
    "byte"    -> toDyn (div :: Word8 -> Word8 -> Word8)
    "intp"    -> toDyn (div :: Int -> Int -> Int)
    _         -> toDyn nil -- means not applicable here
  divByOp :: Text -> Dynamic
  divByOp = \case
    "float64" -> toDyn ((\ !x !y -> y / x) :: Double -> Double -> Double)
    "float32" -> toDyn ((\ !x !y -> y / x) :: Float -> Float -> Float)
    "int64"   -> toDyn ((\ !x !y -> div y x) :: Int64 -> Int64 -> Int64)
    "int32"   -> toDyn ((\ !x !y -> div y x) :: Int32 -> Int32 -> Int32)
    "int8"    -> toDyn ((\ !x !y -> div y x) :: Int8 -> Int8 -> Int8)
    "byte"    -> toDyn ((\ !x !y -> div y x) :: Word8 -> Word8 -> Word8)
    "intp"    -> toDyn ((\ !x !y -> div y x) :: Int -> Int -> Int)
    _         -> toDyn nil -- means not applicable here
  divIntOp :: Text -> Dynamic
  divIntOp = \case
    -- TODO reason about this:
    -- https://stackoverflow.com/questions/38588815/rounding-errors-in-python-floor-division
    "float64" -> toDyn
      ((\ !x !y -> fromInteger $ floor $ x / y) :: Double -> Double -> Double)
    "float32" -> toDyn
      ((\ !x !y -> fromInteger $ floor $ x / y) :: Float -> Float -> Float)
    "int64" -> toDyn (div :: Int64 -> Int64 -> Int64)
    "int32" -> toDyn (div :: Int32 -> Int32 -> Int32)
    "int8"  -> toDyn (div :: Int8 -> Int8 -> Int8)
    "byte"  -> toDyn (div :: Word8 -> Word8 -> Word8)
    "intp"  -> toDyn (div :: Int -> Int -> Int)
    _       -> toDyn nil -- means not applicable here
  divIntByOp :: Text -> Dynamic
  divIntByOp = \case
    "float64" -> toDyn
      ((\ !x !y -> fromInteger $ floor $ y / x) :: Double -> Double -> Double)
    "float32" -> toDyn
      ((\ !x !y -> fromInteger $ floor $ y / x) :: Float -> Float -> Float)
    "int64" -> toDyn ((\ !x !y -> div y x) :: Int64 -> Int64 -> Int64)
    "int32" -> toDyn ((\ !x !y -> div y x) :: Int32 -> Int32 -> Int32)
    "int8"  -> toDyn ((\ !x !y -> div y x) :: Int8 -> Int8 -> Int8)
    "byte"  -> toDyn ((\ !x !y -> div y x) :: Word8 -> Word8 -> Word8)
    "intp"  -> toDyn ((\ !x !y -> div y x) :: Int -> Int -> Int)
    _       -> toDyn nil -- means not applicable here


arangeProc :: Object -> EntityManipulater -> Class -> EdhProcedure
arangeProc !indexDTO !emColumn !clsColumn !apk !exit =
  case parseArgsPack (Nothing, EdhObject indexDTO) argsParser apk of
    Left !err -> throwEdh UsageError err
    Right (Nothing, _) -> throwEdh UsageError "Missing range specification"
    Right (Just !rngSpec, !dtv) -> case rngSpec of
      EdhPair (EdhPair (EdhDecimal !startN) (EdhDecimal !stopN)) (EdhDecimal stepN)
        -> case D.decimalToInteger startN of
          Just !start -> case D.decimalToInteger stopN of
            Just !stop -> case D.decimalToInteger stepN of
              Just !step -> createRangeCol dtv
                                           (fromInteger start)
                                           (fromInteger stop)
                                           (fromInteger step)
              _ -> throwEdh UsageError "step is not an integer"
            _ -> throwEdh UsageError "stop is not an integer"
          _ -> throwEdh UsageError "start is not an integer"
      EdhPair (EdhDecimal !startN) (EdhDecimal !stopN) ->
        case D.decimalToInteger startN of
          Just !start -> case D.decimalToInteger stopN of
            Just !stop ->
              createRangeCol dtv (fromInteger start) (fromInteger stop)
                $ if stop >= start then 1 else -1
            _ -> throwEdh UsageError "stop is not an integer"
          _ -> throwEdh UsageError "start is not an integer"
      EdhDecimal !stopN -> case D.decimalToInteger stopN of
        Just !stop ->
          createRangeCol dtv 0 (fromInteger stop) $ if stop >= 0 then 1 else -1
        _ -> throwEdh UsageError "stop is not an integer"
      _ -> throwEdh UsageError $ "Invalid range of " <> T.pack
        (edhTypeNameOf rngSpec)
 where
  argsParser =
    ArgsPackParser
        [ \arg (_, dtv) -> Right (Just arg, dtv)
        , \arg (spec, _) -> case arg of
          dtv@EdhObject{} -> Right (spec, dtv)
          _               -> Left "Invalid dtype"
        ]
      $ Map.fromList
          [ ( "dtype"
            , \arg (spec, _) -> case arg of
              dtv@EdhObject{} -> Right (spec, dtv)
              _               -> Left "Invalid dtype"
            )
          ]
  createRangeCol :: EdhValue -> Int -> Int -> Int -> EdhProc
  createRangeCol !dtv !start !stop !step = ask >>= \ !pgs ->
    contEdhSTM $ case dtv of
      EdhObject !dto ->
        fromDynamic <$> readTVar (entity'store $ objEntity dto) >>= \case
          Nothing -> throwEdhSTM pgs UsageError "Invalid dtype object"
          Just (ConcreteDataType !dt) ->
            create'range'array dt pgs start stop step $ \ !cs -> do
              !clv    <- newTVar $ flatArrayCapacity cs
              !col    <- Column dt dto clv <$> newTVar cs
              !ent    <- createSideEntity emColumn $ toDyn col
              !colObj <- viewAsEdhObject ent clsColumn []
              exitEdhSTM pgs exit $ EdhObject colObj
      _ -> throwEdhSTM pgs UsageError "Invalid dtype value"


-- TODO impl. `linspace` following:
--      https://numpy.org/doc/stable/reference/generated/numpy.linspace.html
-- Note it can be more exact by stepping with LosslessDecimal

