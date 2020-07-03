
module Dim.Table where

import           Prelude
-- import           Debug.Trace

import           Foreign

import           Control.Monad
import           Control.Monad.Reader
import           Control.Concurrent.STM


-- import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.HashMap.Strict           as Map
import           Data.Dynamic

import           Data.Vector.Storable           ( Vector )
import           Data.Vector.Storable.Mutable   ( IOVector )
import qualified Data.Vector.Storable          as V
import qualified Data.Vector.Storable.Mutable  as MV

import           Data.Lossless.Decimal         as D

import           Language.Edh.EHI

import           Dim.XCHG
import           Dim.DataType


-- | A column is a 1-dimensional array with pre-allocated storage capacity,
-- safely typed for data manipulation.
data Column where
  Column ::(Storable a, EdhXchg a) => {
      -- convey type safe manipulation operations by an instance, making
      -- each column suitable to be wrapped within an untyped Edh object
      column'data'type :: !(DataType a)
      -- column length is number of valid elements, always smaller or equals
      -- to storage vector's length
    , column'length :: !(TVar Int)
      -- mark it obvious that the underlying storage is mutable anytime
      -- length of the Vector should be considered capacity of the column
    , column'storage :: !(TVar (IOVector a))
    } -> Column
 deriving Typeable

createColumn
  :: EdhProgState
  -> ConcreteDataType
  -> Int
  -> TVar Int
  -> (Column -> STM ())
  -> STM ()
createColumn !pgs (ConcreteDataType _ !dt) !cap !clv !exit =
  create'data'vector dt pgs cap
    $ \ !cs -> join $ exit . Column dt clv <$> newTVar cs

columnCapacity :: Column -> STM Int
columnCapacity (Column _ _ !csv) = MV.length <$> readTVar csv

columnLength :: Column -> STM Int
columnLength (Column _ !clv _) = readTVar clv

markColumnLength :: Column -> Int -> STM ()
markColumnLength (Column _ !clv _) !newLen = writeTVar clv newLen

readColumnCell
  :: EdhProgState -> Int -> Column -> (EdhValue -> STM ()) -> STM ()
readColumnCell !pgs !idx (Column !dt _ !csv) !exit =
  readTVar csv >>= \ !cs -> read'data'vector'cell dt pgs idx cs exit

writeColumnCell
  :: EdhProgState -> EdhValue -> Int -> Column -> (EdhValue -> STM ()) -> STM ()
writeColumnCell !pgs !val !idx (Column !dt _ !csv) !exit =
  readTVar csv >>= \ !cs -> write'data'vector'cell dt pgs val idx cs exit

fillColumn
  :: EdhProgState -> EdhValue -> Int -> Int -> Column -> STM () -> STM ()
fillColumn !pgs !val !idxBegin !idxEnd (Column !dt _ !csv) !exit =
  fromEdh pgs val $ \ !sv -> readTVar csv >>= \ !cs -> update'data'vector
    dt
    pgs
    [ (i, sv) | i <- [idxBegin .. idxEnd - 1] ]
    cs
    exit

growColumn :: EdhProgState -> Column -> Int -> STM () -> STM ()
growColumn !pgs (Column !dt !clv !csv) !cap !exit = readTVar csv >>= \ !cs ->
  grow'data'vector dt pgs cs cap $ \ !cs' -> do
    writeTVar csv cs'
    !cl <- readTVar clv
    when (cl > cap) $ writeTVar clv cap
    exit


-- obtain valid column data as an immutable Storable Vector
--
-- this is as unsafe as unsafeFreeze is, pursuing zero-copy performance by
-- sacrificing thread safety
--
-- taking advantage of ForeignPtr under the hood in implementation details,
-- this avoids going through the IO Monad as to convert IOVector to Vector
-- by Data.Vector.Storable.Mutable api
columnData :: forall a . (Storable a, EdhXchg a) => Column -> STM (Vector a)
columnData (Column _ !clv !csv) = do
  !cl <- readTVar clv
  !cs <- readTVar csv
  case MV.unsafeToForeignPtr0 cs of
    (!p, _) -> return $ V.unsafeFromForeignPtr0 (castForeignPtr p) cl


-- | host constructor Column(capacity, length=None, dtype=f8)
colCtor
  :: EdhValue
  -> EdhProgState
  -> ArgsPack  -- ctor args, if __init__() is provided, will go there too
  -> TVar (Map.HashMap AttrKey EdhValue)  -- out-of-band attr store
  -> (Dynamic -> STM ())  -- in-band data to be written to entity store
  -> STM ()
colCtor !defaultDataType !pgsCtor !apk !obs !ctorExit =
  case parseArgsPack (Nothing, -1 :: Int, defaultDataType) ctorArgsParser apk of
    Left err -> throwEdhSTM pgsCtor UsageError err
    Right (Nothing, _, _) -> throwEdhSTM pgsCtor UsageError "Missing capacity"
    Right (Just !cap, !len, !dto) -> do
      let
        !scope = contextScope $ edh'context pgsCtor
        doIt !cdt = do
          methods <- sequence
            [ (AttrByName nm, ) <$> mkHostProc scope vc nm hp mthArgs
            | (nm, vc, hp, mthArgs) <-
              [ ( "grow"
                , EdhMethod
                , colGrowProc
                , PackReceiver [mandatoryArg "newCapacity"]
                )
              , ( "[]"
                , EdhMethod
                , colIdxReadProc
                , PackReceiver [mandatoryArg "idx"]
                )
              , ( "[=]"
                , EdhMethod
                , colIdxWriteProc
                , PackReceiver [mandatoryArg "idx", mandatoryArg "val"]
                )
              , ( "fill"
                , EdhMethod
                , colFillProc
                , PackReceiver [mandatoryArg "val"]
                )
              , ("capacity", EdhMethod, colCapProc, PackReceiver [])
              , ("length"  , EdhMethod, colLenProc, PackReceiver [])
              , ( "markLength"
                , EdhMethod
                , colMarkLenProc
                , PackReceiver [mandatoryArg "newLength"]
                )
              , ("__repr__", EdhMethod, colReprProc, PackReceiver [])
              ]
            ]
          modifyTVar' obs
            $  Map.union
            $  Map.fromList
            $  methods
            ++ [(AttrByName "dtype", dto)]
          lv <- newTVar $ if len < 0 then cap else len
          createColumn pgsCtor cdt cap lv $ \ !col -> ctorExit $ toDyn col
      case dto of
        EdhObject !o ->
          fromDynamic <$> readTVar (entity'store $ objEntity o) >>= \case
            Just cdt@ConcreteDataType{} -> doIt cdt
            _ -> throwEdhSTM pgsCtor UsageError "Missing dtype"
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

  colGrowProc :: EdhProcedure
  colGrowProc (ArgsPack [EdhDecimal !newCapNum] !kwargs) !exit
    | Map.null kwargs = case D.decimalToInteger newCapNum of
      Just !newCap | newCap >= 0 -> do
        pgs <- ask
        let this = thisObject $ contextScope $ edh'context pgs
            es   = entity'store $ objEntity this
        contEdhSTM $ do
          esd <- readTVar es
          case fromDynamic esd of
            Just col@Column{} ->
              growColumn pgs col (fromInteger newCap)
                $ exitEdhSTM pgs exit
                $ EdhObject this
            _ ->
              throwEdhSTM pgs UsageError
                $  "bug: this is not a Column: "
                <> T.pack (show esd)
      _ -> throwEdh UsageError "Column capacity must be a positive integer"
  colGrowProc _ _ = throwEdh UsageError "Invalid args to Column.grow()"

  colIdxReadProc :: EdhProcedure
  colIdxReadProc (ArgsPack !args _) !exit = do
    pgs <- ask
    let this = thisObject $ contextScope $ edh'context pgs
        es   = entity'store $ objEntity this
    contEdhSTM $ do
      esd <- readTVar es
      case fromDynamic esd of
        Just !col -> case args of
          -- TODO support slicing, of coz need to tell a slicing index from
          --      an element index first
          [EdhDecimal !idxNum] -> case D.decimalToInteger idxNum of
            Just !idx ->
              readColumnCell pgs (fromInteger idx) col $ exitEdhSTM pgs exit
            _ ->
              throwEdhSTM pgs UsageError
                $  "Expect an integer to index a Column but you give: "
                <> T.pack (show idxNum)
          _ ->
            throwEdhSTM pgs UsageError
              $  "Invalid index for a Column: "
              <> T.pack (show args)
        _ ->
          throwEdhSTM pgs UsageError $ "bug: this is not a Column: " <> T.pack
            (show esd)

  colIdxWriteProc :: EdhProcedure
  colIdxWriteProc (ArgsPack !args _) !exit = do
    pgs <- ask
    let this = thisObject $ contextScope $ edh'context pgs
        es   = entity'store $ objEntity this
    contEdhSTM $ do
      esd <- readTVar es
      case fromDynamic esd of
        Just !col -> case args of
          -- TODO support slicing assign, of coz need to tell a slicing index
          --      from an element index first
          [EdhDecimal !idxNum, val] -> case D.decimalToInteger idxNum of
            Just !idx ->
              writeColumnCell pgs val (fromInteger idx) col
                $ exitEdhSTM pgs exit
            _ ->
              throwEdhSTM pgs UsageError
                $  "Expect an integer to index a Column but you give: "
                <> T.pack (show idxNum)
          _ ->
            throwEdhSTM pgs UsageError
              $  "Invalid index for a Column: "
              <> T.pack (show args)
        _ ->
          throwEdhSTM pgs UsageError $ "bug: this is not a Column: " <> T.pack
            (show esd)

  colFillProc :: EdhProcedure
  colFillProc (ArgsPack !args _) !exit = do
    pgs <- ask
    let this = thisObject $ contextScope $ edh'context pgs
        es   = entity'store $ objEntity this
    contEdhSTM $ do
      esd <- readTVar es
      case fromDynamic esd of
        Just col@(Column _ !clv _) -> case args of
          -- TODO support slicing assign, of coz need to tell a slicing index
          --      from an element index first
          [val] -> readTVar clv
            >>= \ !cl -> fillColumn pgs val 0 cl col $ exitEdhSTM pgs exit nil
          _ ->
            throwEdhSTM pgs UsageError
              $  "Invalid args for a Column fill: "
              <> T.pack (show args)
        _ ->
          throwEdhSTM pgs UsageError $ "bug: this is not a Column: " <> T.pack
            (show esd)

  colCapProc :: EdhProcedure
  colCapProc _ !exit = do
    pgs <- ask
    let this = thisObject $ contextScope $ edh'context pgs
        es   = entity'store $ objEntity this
    contEdhSTM $ do
      esd <- readTVar es
      case fromDynamic esd of
        Just col@Column{} -> columnCapacity col
          >>= \ !cap -> exitEdhSTM pgs exit $ EdhDecimal $ fromIntegral cap
        _ ->
          throwEdhSTM pgs UsageError $ "bug: this is not a Column: " <> T.pack
            (show esd)

  colLenProc :: EdhProcedure
  colLenProc _ !exit = do
    pgs <- ask
    let this = thisObject $ contextScope $ edh'context pgs
        es   = entity'store $ objEntity this
    contEdhSTM $ do
      esd <- readTVar es
      case fromDynamic esd of
        Just col@Column{} -> columnLength col
          >>= \ !len -> exitEdhSTM pgs exit $ EdhDecimal $ fromIntegral len
        _ ->
          throwEdhSTM pgs UsageError $ "bug: this is not a Column: " <> T.pack
            (show esd)

  colMarkLenProc :: EdhProcedure
  colMarkLenProc (ArgsPack [EdhDecimal !newLenNum] !kwargs) !exit
    | Map.null kwargs = case D.decimalToInteger newLenNum of
      Just !newLen | newLen >= 0 -> do
        pgs <- ask
        let this = thisObject $ contextScope $ edh'context pgs
            es   = entity'store $ objEntity this
        contEdhSTM $ do
          esd <- readTVar es
          case fromDynamic esd of
            Just col@Column{} ->
              markColumnLength col (fromInteger newLen)
                >> exitEdhSTM pgs exit nil
            _ ->
              throwEdhSTM pgs UsageError
                $  "bug: this is not a Column: "
                <> T.pack (show esd)
      _ -> throwEdh UsageError "Column length must be a positive integer"
  colMarkLenProc _ _ =
    throwEdh UsageError "Invalid args to Column.markLength()"

  colReprProc :: EdhProcedure
  colReprProc _ !exit = do
    pgs <- ask
    let
      !this = thisObject $ contextScope $ edh'context pgs
      !es   = entity'store $ objEntity this
      withDtRepr !dtr = do
        esd <- readTVar es
        case fromDynamic esd of
          Just (Column _ !clv !csv) -> do
            !cl <- readTVar clv
            !cs <- readTVar csv
            exitEdhSTM pgs exit
              $  EdhString
              $  "Column("
              <> T.pack (show $ MV.length cs)
              <> ", "
              <> T.pack (show cl)
              <> ", dtype="
              <> dtr
              <> ")"
          _ ->
            throwEdhSTM pgs UsageError $ "bug: this is not a Column: " <> T.pack
              (show esd)
    contEdhSTM $ lookupEdhObjAttr pgs this (AttrByName "dtype") >>= \case
      EdhNil -> withDtRepr "f8" -- this is impossible but just in case
      !dto   -> edhValueReprSTM pgs dto $ \dtr -> withDtRepr dtr

