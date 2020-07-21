
module Dim.Column where

import           Prelude
-- import           Debug.Trace

import           Unsafe.Coerce
import           GHC.Conc                       ( unsafeIOToSTM )

import           Foreign                 hiding ( void )

import           Control.Monad
import           Control.Monad.Reader

import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.HashMap.Strict           as Map

import           Data.Coerce
import           Data.Dynamic

import           Data.Vector.Storable           ( Vector )

import           Data.Lossless.Decimal         as D

import           Language.Edh.EHI

import           Dim.XCHG
import           Dim.DataType


-- | A column is a 1-dimensional array with pre-allocated storage capacity,
-- safely typed for data manipulation.
data Column where
  Column ::(Storable a, Typeable a, EdhXchg a) => {
      -- | Data type identifier used to seek appropriate data manipulation
      -- routines
      column'data'type :: !DataTypeIdent

      -- | column length is number of valid elements, can never be greater than
      -- storage vector's length
      -- this is also the mutex to coordinate concurrent modifications to the
      -- column
    , column'length :: !(TMVar Int)

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
instance Eq Column where
  (Column x'dti _ x'cs) == (Column y'dti _ y'cs) =
    -- note coerce is safe only when dti matches
    x'dti == y'dti && x'cs == coerce y'cs

columnCapacity :: Column -> STM Int
columnCapacity (Column _ _ !csv) = flatArrayCapacity <$> readTVar csv

columnLength :: Column -> STM Int
columnLength (Column _ !clv _) = readTMVar clv

unsafeMarkColumnLength :: Int -> Column -> STM ()
unsafeMarkColumnLength !newLen (Column _ !clv _) = do
  void $ tryTakeTMVar clv
  void $ tryPutTMVar clv newLen

createColumn
  :: EdhProgState
  -> DataTypeIdent
  -> Int
  -> TMVar Int
  -> (Column -> STM ())
  -> STM ()
createColumn !pgs !dti !cap !clv !exit =
  resolveDataType pgs dti $ \(DataType _dti !dtStorable) -> do
    !cs  <- flat'new'array dtStorable cap
    !csv <- newTVar cs
    exit $ Column dti clv csv

growColumn :: EdhProgState -> Int -> Column -> STM () -> STM ()
growColumn !pgs !newCap (Column !dti !clv !csv) !exit =
  resolveDataType pgs dti $ \(DataType _dti !dtStorable) ->
    flip (edhPerformSTM pgs) (const $ contEdhSTM exit) $ do
      !cl  <- takeTMVar clv
      !cs  <- readTVar csv
      !cs' <- flat'grow'array dtStorable (coerce cs) newCap
      writeTVar csv (coerce cs')
      putTMVar clv $ min newCap cl

unsafeReadColumnCell
  :: EdhProgState -> Column -> Int -> (EdhValue -> STM ()) -> STM ()
unsafeReadColumnCell !pgs (Column !dti _ !csv) !idx !exit =
  resolveDataType pgs dti $ \(DataType _dti !dtStorable) -> readTVar csv
    >>= \ !cs -> flat'array'read dtStorable pgs (coerce cs) idx exit

unsafeWriteColumnCell
  :: EdhProgState -> Column -> Int -> EdhValue -> (EdhValue -> STM ()) -> STM ()
unsafeWriteColumnCell !pgs (Column !dti _ !csv) !idx !val !exit =
  resolveDataType pgs dti $ \(DataType _dti !dtStorable) -> readTVar csv
    >>= \ !cs -> flat'array'write dtStorable pgs (coerce cs) idx val exit

unsafeFillColumn
  :: EdhProgState -> Column -> EdhValue -> [Int] -> STM () -> STM ()
unsafeFillColumn !pgs (Column !dti _ !csv) !val !idxs !exit =
  resolveDataType pgs dti $ \(DataType _dti !dtStorable) ->
    fromEdh pgs val $ \ !sv -> readTVar csv >>= \ !cs -> flat'array'update
      dtStorable
      pgs
      [ (i, sv) | i <- idxs ]
      (coerce cs)
      exit

unsafeSliceColumn :: Column -> Int -> Int -> Int -> (Column -> STM ()) -> STM ()
unsafeSliceColumn (Column !dti !clv (csv :: TVar (FlatArray a))) !start !stop !step !exit
  = do
    !cl                     <- readTMVar clv
    cs@(FlatArray !cap !fp) <- readTVar csv
    if start >= cap || stop == start
      then do
        !clv' <- newTMVar 0
        !csv' <- newTVar (emptyFlatArray @a)
        exit $ Column dti clv' csv'
      else if step == 1
        then do
          let !len = max 0 $ min cl stop - start
              !cs' = unsafeSliceFlatArray cs start (cap - start)
          !clv' <- newTMVar len
          !csv' <- newTVar cs'
          exit $ Column dti clv' csv'
        else do
          let (q, r) = quotRem (stop - start) step
              !len   = if r == 0 then abs q else 1 + abs q
          !fp' <- unsafeIOToSTM $ withForeignPtr fp $ \ !p -> do
            !p'  <- callocArray @a len
            !fp' <- newForeignPtr finalizerFree p'
            let fillRng :: Int -> Int -> IO ()
                fillRng !n !i = if i >= len
                  then return ()
                  else do
                    peekElemOff p n >>= pokeElemOff p' i
                    fillRng (n + step) (i + 1)
            fillRng start 0
            return fp'
          let !cs' = FlatArray len fp'
          !csv' <- newTVar cs'
          !clv' <- newTMVar len
          exit $ Column dti clv' csv'


extractColumnBool
  :: EdhProgState -> Column -> Column -> STM () -> (Column -> STM ()) -> STM ()
extractColumnBool !pgs (Column _mdti !mclv !mcsv) (Column !dti !clv !csv) !naExit !exit
  = do
    !cl <- readTMVar clv
    !cs <- readTVar csv
    resolveDataOperator' pgs dti cs naExit $ \ !dtOp -> do
      let !fa = unsafeSliceFlatArray cs 0 cl
      !mcl <- readTMVar mclv
      if mcl /= cl
        then
          throwEdhSTM pgs UsageError
          $  "Index length mismatch: "
          <> T.pack (show mcl)
          <> " vs "
          <> T.pack (show cl)
        else do
          !mcs <- readTVar mcsv
          let !ma = unsafeSliceFlatArray mcs 0 mcl
          flat'extract'bool dtOp pgs (unsafeCoerce ma) fa $ \(!rfa, !rlen) -> do
            !clvRtn <- newTMVar rlen
            !csvRtn <- newTVar rfa
            exit $ Column dti clvRtn csvRtn


extractColumnFancy
  :: EdhProgState -> Column -> Column -> STM () -> (Column -> STM ()) -> STM ()
extractColumnFancy !pgs (Column _idti !iclv !icsv) (Column !dti !clv !csv) !naExit !exit
  = do
    !icl <- readTMVar iclv
    !ics <- readTVar icsv
    !cl  <- readTMVar clv
    !cs  <- readTVar csv
    resolveDataOperator' pgs dti cs naExit $ \ !dtOp -> do
      let !ifa = unsafeSliceFlatArray (coerce ics) 0 icl
          !fa  = unsafeSliceFlatArray cs 0 cl
      flat'extract'fancy dtOp pgs ifa fa $ \ !rfa -> do
        !clvRtn <- newTMVar icl
        !csvRtn <- newTVar rfa
        exit $ Column dti clvRtn csvRtn


vecCmpColumn
  :: EdhProgState
  -> (Ordering -> Bool)
  -> Column
  -> EdhValue
  -> (Column -> STM ())
  -> STM ()
vecCmpColumn !pgs !cmp (Column !dti !clv !csv) !v !exit = do
  !cl <- readTMVar clv
  !cs <- readTVar csv
  resolveDataComparator pgs dti cs $ \ !dtOrd -> do
    let !fa = unsafeSliceFlatArray cs 0 cl
    flat'cmp'vectorized dtOrd pgs fa cmp v $ \ !bifa -> do
      !biclv <- newTMVar cl
      !bicsv <- newTVar bifa
      exit $ Column "bool" biclv bicsv

elemCmpColumn
  :: EdhProgState
  -> (Ordering -> Bool)
  -> Column
  -> Column
  -> (Column -> STM ())
  -> STM ()
elemCmpColumn !pgs !cmp (Column !dti1 !clv1 !csv1) (Column !dti2 !clv2 !csv2) !exit
  = if dti1 /= dti2
    then
      throwEdhSTM pgs UsageError
      $  "Column dtype mismatch: "
      <> dti1
      <> " vs "
      <> dti2
    else do
      !cl1 <- readTMVar clv1
      !cl2 <- readTMVar clv2
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
          resolveDataComparator pgs dti1 cs1 $ \ !dtOrd -> do
            let !fa1 = unsafeSliceFlatArray cs1 0 cl1
                !fa2 = unsafeSliceFlatArray cs2 0 cl2
            flat'cmp'element'wise dtOrd pgs fa1 cmp (unsafeCoerce fa2)
              $ \ !bifa -> do
                  !biclv <- newTMVar cl1
                  !bicsv <- newTVar bifa
                  exit $ Column "bool" biclv bicsv

vecOpColumn
  :: EdhProgState
  -> (Text -> Dynamic)
  -> Column
  -> EdhValue
  -> STM ()
  -> (Column -> STM ())
  -> STM ()
vecOpColumn !pgs !getOp (Column !dti !clv !csv) !v !naExit !exit = do
  !cl <- readTMVar clv
  !cs <- readTVar csv
  resolveDataOperator' pgs dti cs naExit $ \ !dtOp -> do
    let !fa  = unsafeSliceFlatArray cs 0 cl
    let !dop = getOp dti
    case fromDynamic dop of
      Just EdhNil -> naExit
      _           -> flat'op'vectorized dtOp pgs fa dop v $ \ !bifa -> do
        !biclv <- newTMVar cl
        !bicsv <- newTVar bifa
        exit $ Column dti biclv bicsv

elemOpColumn
  :: EdhProgState
  -> (Text -> Dynamic)
  -> Column
  -> Column
  -> STM ()
  -> (Column -> STM ())
  -> STM ()
elemOpColumn !pgs !getOp (Column !dti1 !clv1 !csv1) (Column !dti2 !clv2 !csv2) !naExit !exit
  = if dti1 /= dti2
    then
      throwEdhSTM pgs UsageError
      $  "Column dtype mismatch: "
      <> dti1
      <> " vs "
      <> dti2
    else do
      !cl1 <- readTMVar clv1
      !cl2 <- readTMVar clv2
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
          resolveDataOperator' pgs dti1 cs1 naExit $ \ !dtOp -> do
            let !fa1 = unsafeSliceFlatArray cs1 0 cl1
                !fa2 = unsafeSliceFlatArray cs2 0 cl2
            let !dop = getOp dti1
            case fromDynamic dop of
              Just EdhNil -> naExit
              _ ->
                flat'op'element'wise dtOp pgs fa1 dop (unsafeCoerce fa2)
                  $ \ !bifa -> do
                      !biclv <- newTMVar cl1
                      !bicsv <- newTVar bifa
                      exit $ Column dti1 biclv bicsv

vecInpColumn
  :: EdhProgState
  -> (Text -> Dynamic)
  -> Column
  -> EdhValue
  -> STM ()
  -> STM ()
  -> STM ()
vecInpColumn !pgs !getOp (Column !dti !clv !csv) !v !naExit !exit = do
  !cl <- readTMVar clv
  !cs <- readTVar csv
  resolveDataOperator' pgs dti cs naExit $ \ !dtOp -> do
    let !fa  = unsafeSliceFlatArray cs 0 cl
    let !dop = getOp dti
    case fromDynamic dop of
      Just EdhNil -> naExit
      _           -> flat'inp'vectorized dtOp pgs fa dop v exit

vecInpSliceColumn
  :: EdhProgState
  -> (Int, Int, Int)
  -> (Text -> Dynamic)
  -> Column
  -> EdhValue
  -> STM ()
  -> STM ()
  -> STM ()
vecInpSliceColumn !pgs !slice !getOp (Column !dti !clv !csv) !v !naExit !exit =
  do
    !cl <- readTMVar clv
    !cs <- readTVar csv
    resolveDataOperator' pgs dti cs naExit $ \ !dtOp -> do
      let !fa  = unsafeSliceFlatArray cs 0 cl
      let !dop = getOp dti
      case fromDynamic dop of
        Just EdhNil -> naExit
        _           -> flat'inp'vectorized'slice dtOp pgs slice fa dop v exit

vecInpMaskedColumn
  :: EdhProgState
  -> Column
  -> (Text -> Dynamic)
  -> Column
  -> EdhValue
  -> STM ()
  -> STM ()
  -> STM ()
vecInpMaskedColumn !pgs (Column _ !mclv !mcsv) !getOp (Column !dti !clv !csv) !v !naExit !exit
  = do
    !cl <- readTMVar clv
    !cs <- readTVar csv
    resolveDataOperator' pgs dti cs naExit $ \ !dtOp -> do
      let !fa  = unsafeSliceFlatArray cs 0 cl
      let !dop = getOp dti
      case fromDynamic dop of
        Just EdhNil -> naExit
        _           -> do
          !mcl <- readTMVar mclv
          if mcl /= cl
            then
              throwEdhSTM pgs UsageError
              $  "Index length mismatch: "
              <> T.pack (show mcl)
              <> " vs "
              <> T.pack (show cl)
            else do
              !mcs <- readTVar mcsv
              let !ma = unsafeSliceFlatArray mcs 0 mcl
              flat'inp'vectorized'masked dtOp
                                         pgs
                                         (unsafeCoerce ma)
                                         fa
                                         dop
                                         v
                                         exit

vecInpFancyColumn
  :: EdhProgState
  -> Column
  -> (Text -> Dynamic)
  -> Column
  -> EdhValue
  -> STM ()
  -> STM ()
  -> STM ()
vecInpFancyColumn !pgs (Column _ !iclv !icsv) !getOp (Column !dti !clv !csv) !v !naExit !exit
  = do
    !cl <- readTMVar clv
    !cs <- readTVar csv
    resolveDataOperator' pgs dti cs naExit $ \ !dtOp -> do
      let !fa  = unsafeSliceFlatArray cs 0 cl
      let !dop = getOp dti
      case fromDynamic dop of
        Just EdhNil -> naExit
        _           -> do
          !icl <- readTMVar iclv
          !ics <- readTVar icsv
          let !ia = unsafeSliceFlatArray ics 0 icl
          flat'inp'vectorized'fancy dtOp pgs (unsafeCoerce ia) fa dop v exit

elemInpColumn
  :: EdhProgState
  -> (Text -> Dynamic)
  -> Column
  -> Column
  -> STM ()
  -> STM ()
  -> STM ()
elemInpColumn !pgs !getOp (Column !dti1 !clv1 !csv1) (Column !dti2 !clv2 !csv2) !naExit !exit
  = if dti1 /= dti2
    then
      throwEdhSTM pgs UsageError
      $  "Column dtype mismatch: "
      <> dti1
      <> " vs "
      <> dti2
    else do
      !cl1 <- readTMVar clv1
      !cl2 <- readTMVar clv2
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
          resolveDataOperator' pgs dti1 cs1 naExit $ \ !dtOp -> do
            let !fa1 = unsafeSliceFlatArray cs1 0 cl1
                !fa2 = unsafeSliceFlatArray cs2 0 cl2
            let !dop = getOp dti1
            case fromDynamic dop of
              Just EdhNil -> naExit
              _ ->
                flat'inp'element'wise dtOp pgs fa1 dop (unsafeCoerce fa2) exit

elemInpSliceColumn
  :: EdhProgState
  -> (Int, Int, Int)
  -> (Text -> Dynamic)
  -> Column
  -> Column
  -> STM ()
  -> STM ()
  -> STM ()
elemInpSliceColumn !pgs !slice !getOp (Column !dti1 !clv1 !csv1) (Column !dti2 !clv2 !csv2) !naExit !exit
  = if dti1 /= dti2
    then
      throwEdhSTM pgs UsageError
      $  "Column dtype mismatch: "
      <> dti1
      <> " vs "
      <> dti2
    else do
      !cl1 <- readTMVar clv1
      !cl2 <- readTMVar clv2
      !cs1 <- readTVar csv1
      !cs2 <- readTVar csv2
      resolveDataOperator' pgs dti1 cs1 naExit $ \ !dtOp -> do
        let !fa1 = unsafeSliceFlatArray cs1 0 cl1
            !fa2 = unsafeSliceFlatArray cs2 0 cl2
        let !dop = getOp dti1
        case fromDynamic dop of
          Just EdhNil -> naExit
          _           -> flat'inp'element'wise'slice dtOp
                                                     pgs
                                                     slice
                                                     fa1
                                                     dop
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
elemInpMaskedColumn !pgs (Column _ !mclv !mcsv) !getOp (Column !dti1 !clv1 !csv1) (Column !dti2 !clv2 !csv2) !naExit !exit
  = if dti1 /= dti2
    then
      throwEdhSTM pgs UsageError
      $  "Column dtype mismatch: "
      <> dti1
      <> " vs "
      <> dti2
    else do
      !cl1 <- readTMVar clv1
      !cl2 <- readTMVar clv2
      if cl1 /= cl2
        then
          throwEdhSTM pgs UsageError
          $  "Column length mismatch: "
          <> T.pack (show cl1)
          <> " vs "
          <> T.pack (show cl2)
        else do
          !mcl <- readTMVar mclv
          !mcs <- readTVar mcsv
          !cs1 <- readTVar csv1
          !cs2 <- readTVar csv2
          resolveDataOperator' pgs dti1 cs1 naExit $ \ !dtOp -> do
            let !ma  = unsafeSliceFlatArray mcs 0 mcl
                !fa1 = unsafeSliceFlatArray cs1 0 cl1
                !fa2 = unsafeSliceFlatArray cs2 0 cl2
            let !dop = getOp dti1
            case fromDynamic dop of
              Just EdhNil -> naExit
              _           -> flat'inp'element'wise'masked dtOp
                                                          pgs
                                                          (unsafeCoerce ma)
                                                          fa1
                                                          dop
                                                          (unsafeCoerce fa2)
                                                          exit

elemInpFancyColumn
  :: EdhProgState
  -> Column
  -> (Text -> Dynamic)
  -> Column
  -> Column
  -> STM ()
  -> STM ()
  -> STM ()
elemInpFancyColumn !pgs (Column _ !iclv !icsv) !getOp (Column !dti1 !clv1 !csv1) (Column !dti2 !clv2 !csv2) !naExit !exit
  = if dti1 /= dti2
    then
      throwEdhSTM pgs UsageError
      $  "Column dtype mismatch: "
      <> dti1
      <> " vs "
      <> dti2
    else do
      !cl1 <- readTMVar clv1
      !cl2 <- readTMVar clv2
      if cl1 /= cl2
        then
          throwEdhSTM pgs UsageError
          $  "Column length mismatch: "
          <> T.pack (show cl1)
          <> " vs "
          <> T.pack (show cl2)
        else do
          !icl <- readTMVar iclv
          !ics <- readTVar icsv
          !cs1 <- readTVar csv1
          !cs2 <- readTVar csv2
          resolveDataOperator' pgs dti1 cs1 naExit $ \ !dtOp -> do
            let !ia  = unsafeSliceFlatArray ics 0 icl
                !fa1 = unsafeSliceFlatArray cs1 0 cl1
                !fa2 = unsafeSliceFlatArray cs2 0 cl2
            let !dop = getOp dti1
            case fromDynamic dop of
              Just EdhNil -> naExit
              _           -> flat'inp'element'wise'fancy dtOp
                                                         pgs
                                                         (unsafeCoerce ia)
                                                         fa1
                                                         dop
                                                         (unsafeCoerce fa2)
                                                         exit


nonzeroIdxColumn :: EdhProgState -> Column -> (Column -> STM ()) -> STM ()
nonzeroIdxColumn !pgs (Column _mdti !mclv !mcsv) !exit =
  resolveNumDataType pgs "intp" $ \(NumDataType _dti !dtRanger) -> do
    !mcl <- readTMVar mclv
    !mcs <- readTVar mcsv
    let !ma = unsafeSliceFlatArray mcs 0 mcl
    flat'new'nonzero'array dtRanger pgs (unsafeCoerce ma) $ \(!rfa, !rlen) -> do
      !clvRtn <- newTMVar rlen
      !csvRtn <- newTVar rfa
      exit $ Column "intp" clvRtn csvRtn


-- obtain valid column data as an immutable Storable Vector
-- this is unsafe in both memory/type regards and thread regard
unsafeCastColumnData
  :: forall a . (Storable a, EdhXchg a) => Column -> STM (Vector a)
unsafeCastColumnData (Column _ _ !csv) = do
  !ary <- readTVar csv
  return $ unsafeFlatArrayAsVector ary


-- | host constructor Column(capacity, length=None, dtype=f8)
colCtor :: EdhHostCtor
colCtor !pgsCtor !apk !ctorExit =
  case parseArgsPack (Nothing, -1 :: Int, "float64") ctorArgsParser apk of
    Left !err -> throwEdhSTM pgsCtor UsageError err
    Right (Nothing, _, _) -> throwEdhSTM pgsCtor UsageError "Missing capacity"
    Right (Just !cap, !len, !dti) -> do
      lv <- newTMVar $ if len < 0 then cap else len
      createColumn pgsCtor dti cap lv (ctorExit . toDyn)
 where
  ctorArgsParser =
    ArgsPackParser
        [ \arg (_, len, dti) -> case arg of
          EdhDecimal !capVal -> case D.decimalToInteger capVal of
            Just !cap | cap >= 0 -> Right (Just $ fromInteger cap, len, dti)
            _ -> Left "Expect a positive interger for capacity"
          _ -> Left "Invalid capacity"
        , \arg (cap, _, dti) -> case arg of
          EdhDecimal !lenVal -> case D.decimalToInteger lenVal of
            Just !len | len >= 0 -> Right (cap, fromIntegral len, dti)
            _                    -> Left "Expect a positive interger for length"
          _ -> Left "Invalid length"
        , \arg (cap, len, _) -> case edhUltimate arg of
          EdhString !dti -> Right (cap, len, dti)
          _              -> Left "Invalid dtype"
        ]
      $ Map.fromList
          [ ( "length"
            , \arg (cap, _, dti) -> case arg of
              EdhDecimal !lenVal -> case D.decimalToInteger lenVal of
                Just !len | len >= 0 -> Right (cap, fromInteger len, dti)
                _ -> Left "Expect a positive interger for length"
              _ -> Left "Invalid length"
            )
          , ( "dtype"
            , \arg (cap, len, _) -> case arg of
              EdhString !dti -> Right (cap, len, dti)
              _              -> Left "Invalid dtype"
            )
          ]

colMethods :: EdhProgState -> STM [(AttrKey, EdhValue)]
colMethods !pgsModule =
  sequence
    $  [ (AttrByName nm, ) <$> mkHostProc scope vc nm hp mthArgs
       | (nm, vc, hp, mthArgs) <-
         [ ("__cap__", EdhMethod, colCapProc, PackReceiver [])
         , ( "__grow__"
           , EdhMethod
           , colGrowProc
           , PackReceiver [mandatoryArg "newCapacity"]
           )
         , ("__len__", EdhMethod, colLenProc, PackReceiver [])
         , ( "__mark__"
           , EdhMethod
           , colMarkLenProc
           , PackReceiver [mandatoryArg "newLength"]
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
       | (nm, getter, setter) <- [("dtype", colDtypeProc, Nothing)]
       ]
 where
  !scope = contextScope $ edh'context pgsModule

  colGrowProc :: EdhProcedure
  colGrowProc (ArgsPack [EdhDecimal !newCapNum] !kwargs) !exit | odNull kwargs =
    case D.decimalToInteger newCapNum of
      Just !newCap | newCap > 0 -> withThatEntity $ \ !pgs !col ->
        growColumn pgs (fromInteger newCap) col
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
    | odNull kwargs = withThatEntity $ \ !pgs !col -> do
      !cap <- columnCapacity col
      case D.decimalToInteger newLenNum of
        Just !newLen | newLen >= 0 && newLen <= fromIntegral cap ->
          unsafeMarkColumnLength (fromInteger newLen) col
            >> exitEdhSTM pgs exit nil
        _ -> throwEdhSTM pgs UsageError "Column length out of range"
  colMarkLenProc _ _ =
    throwEdh UsageError "Invalid args to Column.markLength()"

  colDtypeProc :: EdhProcedure
  colDtypeProc _ !exit = withThatEntity
    $ \ !pgs (Column !dti _ _) -> exitEdhSTM pgs exit $ EdhString dti

  colReprProc :: EdhProcedure
  colReprProc _ !exit =
    withThatEntity' (\ !pgs -> exitEdhSTM pgs exit $ EdhString "<bogus-Column>")
      $ \ !pgs (Column !dti !clv !csv) -> do
          !cl <- readTMVar clv
          !cs <- readTVar csv
          exitEdhSTM pgs exit
            $  EdhString
            $  "Column("
            <> T.pack (show $ flatArrayCapacity cs)
            <> ", length="
            <> T.pack (show cl)
            <> ", dtype="
            <> dti -- assuming the identifier is available as attr
            <> ")"

  colShowProc :: EdhProcedure
  colShowProc _ !exit = withThatEntity $ \ !pgs (Column !dti !clv !csv) ->
    resolveDataType pgs dti $ \(DataType _dti !dtStorable) -> do
      !cl <- readTMVar clv
      !cs <- readTVar csv
      showData pgs cl $ flat'array'read dtStorable pgs (coerce cs)
   where
    showData
      :: EdhProgState
      -> Int
      -> (Int -> (EdhValue -> STM ()) -> STM ())
      -> STM ()
    showData !pgs !len !readElem = go 0 [] 0 ""
     where
      go :: Int -> [Text] -> Int -> Text -> STM ()
      -- TODO don't generate all lines for large columns
      go !i !cumLines !lineIdx !line | i >= len =
        exitEdhSTM pgs exit $ EdhString $ if T.null line && null cumLines
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
      go !i !cumLines !lineIdx !line = readElem i $ \ !elemVal ->
        edhValueReprSTM pgs elemVal $ \ !elemRepr ->
          let !tentLine = line <> elemRepr <> ", "
          in  if T.length tentLine > 79 -- todo make this tunable ?
                then go
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
                else go (i + 1) cumLines lineIdx tentLine

  -- TODO impl. this following:
  --      https://pandas.pydata.org/pandas-docs/stable/reference/api/pandas.Series.describe.html
  colDescProc :: EdhProcedure
  colDescProc _ !exit =
    exitEdhProc exit
      $  EdhString
      $  " * Statistical Description of Column data,\n"
      <> "   like pandas describe(), is yet to be implemented."


  colIdxReadProc :: EdhProcedure
  colIdxReadProc (ArgsPack [!idxVal] !kwargs) !exit | odNull kwargs =
    withThatEntity $ \ !pgs !col -> do
      let colObj = thatObject $ contextScope $ edh'context pgs
      castObjectStore' idxVal >>= \case
        Just !idxCol -> case column'data'type idxCol of
          "bool" -> -- bool index 
            extractColumnBool pgs idxCol col (exitEdhSTM pgs exit EdhContinue)
              $ \ !colResult ->
                  cloneEdhObject colObj
                                 (\_ !cloneTo -> cloneTo $ toDyn colResult)
                    $ \ !newObj -> exitEdhSTM pgs exit $ EdhObject newObj
          "intp" -> -- fancy index 
            extractColumnFancy pgs idxCol col (exitEdhSTM pgs exit EdhContinue)
              $ \ !colResult ->
                  cloneEdhObject colObj
                                 (\_ !cloneTo -> cloneTo $ toDyn colResult)
                    $ \ !newObj -> exitEdhSTM pgs exit $ EdhObject newObj
          !badDti ->
            throwEdhSTM pgs UsageError
              $  "Invalid dtype="
              <> badDti
              <> " for a column as an index to another column"
        Nothing -> parseEdhIndex pgs idxVal $ \case
          Left !err -> throwEdhSTM pgs UsageError err
          Right (EdhIndex !i) ->
            unsafeReadColumnCell pgs col i $ exitEdhSTM pgs exit
          Right EdhAny -> exitEdhSTM pgs exit $ EdhObject colObj
          Right EdhAll -> exitEdhSTM pgs exit $ EdhObject colObj
          Right (EdhSlice !start !stop !step) -> do
            !cl <- columnLength col
            edhRegulateSlice pgs cl (start, stop, step)
              $ \(!iStart, !iStop, !iStep) ->
                  unsafeSliceColumn col iStart iStop iStep $ \ !newCol ->
                    cloneEdhObject colObj
                                   (\_ !cloneTo -> cloneTo $ toDyn newCol)
                      $ \ !newObj -> exitEdhSTM pgs exit $ EdhObject newObj
  colIdxReadProc !apk _ =
    throwEdh UsageError $ "Invalid indexing syntax for a Column: " <> T.pack
      (show apk)

  colIdxWriteProc :: EdhProcedure
  colIdxWriteProc (ArgsPack [!idxVal, !other] !kwargs) !exit | odNull kwargs =
    withThatEntity $ \ !pgs col@(Column !dti !clv _csv) -> do
      let colObj = thatObject $ contextScope $ edh'context pgs
      castObjectStore' (edhUltimate other) >>= \case
        -- assign column to column
        Just colOther@(Column !dtiOther !clvOther _) -> if dtiOther /= dti
          then
            throwEdhSTM pgs UsageError
            $  "Assigning column of dtype="
            <> dtiOther
            <> " to "
            <> dti
            <> " not supported."
          else castObjectStore' idxVal >>= \case
            Just !idxCol -> case column'data'type idxCol of
              "bool" -> -- bool index 
                elemInpMaskedColumn pgs
                                    idxCol
                                    assignOp
                                    col
                                    colOther
                                    (exitEdhSTM pgs exit EdhContinue)
                  $ exitEdhSTM pgs exit
                  $ EdhObject colObj
              "intp" -> -- fancy index 
                elemInpFancyColumn pgs
                                   idxCol
                                   assignOp
                                   col
                                   colOther
                                   (exitEdhSTM pgs exit EdhContinue)
                  $ exitEdhSTM pgs exit
                  $ EdhObject colObj
              !badDti ->
                throwEdhSTM pgs UsageError
                  $  "Invalid dtype="
                  <> badDti
                  <> " for a column as an index to another column"
            Nothing -> parseEdhIndex pgs idxVal $ \case
              Left  !err         -> throwEdhSTM pgs UsageError err
              Right (EdhIndex _) -> throwEdhSTM
                pgs
                UsageError
                "Can not assign a column to a single index of another column"
              Right EdhAny -> throwEdhSTM
                pgs
                UsageError
                "Can not assign a column to every element of another column"
              Right EdhAll -> if dtiOther /= dti
                then
                  throwEdhSTM pgs UsageError
                  $  "Assigning column of dtype="
                  <> dtiOther
                  <> " to "
                  <> dti
                  <> " not supported."
                else do
                  !cl      <- readTMVar clv
                  !clOther <- readTMVar clvOther
                  if clOther /= cl
                    then
                      throwEdhSTM pgs UsageError
                      $  "Column length mismatch: "
                      <> T.pack (show clOther)
                      <> " vs "
                      <> T.pack (show cl)
                    else
                      elemInpColumn pgs
                                    assignOp
                                    col
                                    colOther
                                    (exitEdhSTM pgs exit EdhContinue)
                      $ exitEdhSTM pgs exit
                      $ EdhObject colObj
              Right (EdhSlice !start !stop !step) -> do
                !cl <- columnLength col
                edhRegulateSlice pgs cl (start, stop, step) $ \ !slice ->
                  elemInpSliceColumn pgs
                                     slice
                                     assignOp
                                     col
                                     colOther
                                     (exitEdhSTM pgs exit EdhContinue)
                    $ exitEdhSTM pgs exit other

        -- assign scalar to column
        Nothing -> castObjectStore' idxVal >>= \case
          Just idxCol@(Column !dtiIdx _clvIdx _csvIdx) -> case dtiIdx of
            "bool" -> -- bool index 
              vecInpMaskedColumn pgs
                                 idxCol
                                 assignOp
                                 col
                                 (edhUltimate other)
                                 (exitEdhSTM pgs exit EdhContinue)
                $ exitEdhSTM pgs exit
                $ EdhObject colObj
            "intp" -> -- fancy index
              vecInpFancyColumn pgs
                                idxCol
                                assignOp
                                col
                                (edhUltimate other)
                                (exitEdhSTM pgs exit EdhContinue)
                $ exitEdhSTM pgs exit
                $ EdhObject colObj
            !badDti ->
              throwEdhSTM pgs UsageError
                $  "Invalid dtype="
                <> badDti
                <> " for a column as an index to another column"
          Nothing -> parseEdhIndex pgs idxVal $ \case
            Left !err -> throwEdhSTM pgs UsageError err
            Right (EdhIndex !i) ->
              unsafeWriteColumnCell pgs col i (edhUltimate other)
                $ exitEdhSTM pgs exit
            Right EdhAny -> do
              !cl <- columnLength col
              unsafeFillColumn pgs col (edhUltimate other) [0 .. cl - 1]
                $ exitEdhSTM pgs exit
                $ EdhObject colObj
            Right EdhAll -> do
              !cl <- columnLength col
              unsafeFillColumn pgs col (edhUltimate other) [0 .. cl - 1]
                $ exitEdhSTM pgs exit
                $ EdhObject colObj
            Right (EdhSlice !start !stop !step) -> do
              !cl <- columnLength col
              edhRegulateSlice pgs cl (start, stop, step)
                $ \(!iStart, !iStop, !iStep) ->
                    vecInpSliceColumn pgs
                                      (iStart, iStop, iStep)
                                      assignOp
                                      col
                                      (edhUltimate other)
                                      (exitEdhSTM pgs exit EdhContinue)
                      $ exitEdhSTM pgs exit
                      $ EdhObject colObj

  colIdxWriteProc !apk _ =
    throwEdh UsageError
      $  "Invalid assigning indexing syntax for a Column: "
      <> T.pack (show apk)


  colCmpProc :: (Ordering -> Bool) -> EdhProcedure
  colCmpProc !cmp (ArgsPack [!other] _) !exit =
    withThatEntity $ \ !pgs !col -> case edhUltimate other of
      otherVal@(EdhObject !otherObj) ->
        fromDynamic <$> objStore otherObj >>= \case
          Just colOther@Column{} ->
            elemCmpColumn pgs cmp col colOther $ \ !colResult ->
              cloneEdhObject (thatObject $ contextScope $ edh'context pgs)
                             (\_ !esdx -> esdx $ toDyn colResult)
                $ \ !bio -> exitEdhSTM pgs exit $ EdhObject bio
          Nothing -> vecCmpColumn pgs cmp col otherVal $ \ !colResult ->
            cloneEdhObject (thatObject $ contextScope $ edh'context pgs)
                           (\_ !esdx -> esdx $ toDyn colResult)
              $ \ !bio -> exitEdhSTM pgs exit $ EdhObject bio
      !otherVal -> vecCmpColumn pgs cmp col otherVal $ \ !colResult ->
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
      let colObj = thatObject $ contextScope $ edh'context pgs
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
                  $ EdhObject colObj
              Nothing ->
                vecInpColumn pgs
                             getOp
                             col
                             otherVal
                             (exitEdhSTM pgs exit EdhContinue)
                  $ exitEdhSTM pgs exit
                  $ EdhObject colObj
          !otherVal ->
            vecInpColumn pgs
                         getOp
                         col
                         otherVal
                         (exitEdhSTM pgs exit EdhContinue)
              $ exitEdhSTM pgs exit
              $ EdhObject colObj
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


arangeProc :: Object -> EdhProcedure
arangeProc !colTmplObj !apk !exit =
  case parseArgsPack (Nothing, "intp") argsParser apk of
    Left !err -> throwEdh UsageError err
    Right (Nothing, _) -> throwEdh UsageError "Missing range specification"
    Right (Just !rngSpec, !dtv) -> case edhUltimate rngSpec of
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
      !badRngSpec -> ask >>= \ !pgs ->
        contEdhSTM $ edhValueReprSTM pgs badRngSpec $ \ !rngRepr ->
          throwEdhSTM pgs UsageError
            $  "Invalid range of "
            <> T.pack (edhTypeNameOf badRngSpec)
            <> ": "
            <> rngRepr
 where
  argsParser =
    ArgsPackParser
        [ \arg (_, dti) -> Right (Just arg, dti)
        , \arg (spec, _) -> case edhUltimate arg of
          EdhString !dti -> Right (spec, dti)
          _              -> Left "Invalid dtype"
        ]
      $ Map.fromList
          [ ( "dtype"
            , \arg (spec, _) -> case edhUltimate arg of
              EdhString !dti -> Right (spec, dti)
              _              -> Left "Invalid dtype"
            )
          ]
  createRangeCol :: DataTypeIdent -> Int -> Int -> Int -> EdhProc
  createRangeCol !dti !start !stop !step = ask >>= \ !pgs ->
    contEdhSTM $ resolveNumDataType pgs dti $ \(NumDataType _dti !dtRanger) ->
      flat'new'range'array dtRanger pgs start stop step $ \ !cs -> do
        !clv <- newTMVar $ flatArrayCapacity cs
        !csv <- newTVar cs
        let !col = Column dti clv csv
        cloneEdhObject colTmplObj (\_ !cloneExit -> cloneExit $ toDyn col)
          $ \ !colObj -> exitEdhSTM pgs exit $ EdhObject colObj


-- TODO impl. `linspace` following:
--      https://numpy.org/doc/stable/reference/generated/numpy.linspace.html
-- Note it can be more exact by stepping with LosslessDecimal


-- | resemble https://numpy.org/doc/stable/reference/generated/numpy.where.html
whereProc :: EdhProcedure
whereProc (ArgsPack [EdhObject !colBoolIdx] !kwargs) !exit | odNull kwargs =
  ask >>= \ !pgs -> contEdhSTM $ fromDynamic <$> objStore colBoolIdx >>= \case
    Nothing -> throwEdhSTM
      pgs
      UsageError
      "Invalid index object, need to be a column with dtype=bool"
    Just mcol@(Column !dti _ _) -> if dti /= "bool"
      then
        throwEdhSTM pgs UsageError
        $  "Invalid dtype="
        <> dti
        <> " for where(), need to be bool"
      else nonzeroIdxColumn pgs mcol $ \ !colResult ->
        cloneEdhObject colBoolIdx (\_ !cloneTo -> cloneTo $ toDyn colResult)
          $ \ !newObj -> exitEdhSTM pgs exit $ EdhObject newObj
whereProc (ArgsPack [EdhObject !_colBoolIdx, !_trueData, !_falseData] !kwargs) !_exit
  | odNull kwargs
  = throwEdh UsageError "Not implemented yet."
whereProc !apk _ =
  throwEdh UsageError $ "Invalid args to where()" <> T.pack (show apk)

