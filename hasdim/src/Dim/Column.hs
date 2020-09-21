
module Dim.Column where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           GHC.Float

import           Foreign                 hiding ( void )

import           Control.Monad

import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import qualified Data.Text                     as T

import           Data.Dynamic

import qualified Data.Vector.Mutable           as MV
import qualified Data.Vector.Storable          as VS
import qualified Data.Vector.Storable.Mutable  as MVS

import           Data.Lossless.Decimal         as D

import           Language.Edh.EHI

import           Language.Edh.Batteries

import           Dim.XCHG
import           Dim.DataType


-- | A column is a 1-dimensional array with pre-allocated storage capacity,
-- safely typed for data manipulation.
data Column where
  Column ::{
      -- | Data type
      column'data'type :: !DataType

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
    , column'storage :: !(TVar FlatArray)
    } -> Column
instance Eq Column where
  (Column !x'dt _ x'cs) == (Column !y'dt _ y'cs) =
    -- note coerce is safe only when dti matches
    data'type'identifier x'dt == data'type'identifier y'dt && x'cs == y'cs

columnCapacity :: Column -> STM Int
columnCapacity (Column _ _ !csv) = flatArrayCapacity <$> readTVar csv

columnLength :: Column -> STM Int
columnLength (Column _ !clv _) = readTMVar clv

unsafeMarkColumnLength :: Int -> Column -> STM ()
unsafeMarkColumnLength !newLen (Column _ !clv _) = do
  void $ tryTakeTMVar clv
  void $ tryPutTMVar clv newLen

createColumn
  :: EdhThreadState
  -> DataType
  -> Int
  -> TMVar Int
  -> (Column -> STM ())
  -> STM ()
createColumn _ets !dt !cap !clv !exit = do
  !cs  <- flat'new'array dt cap
  !csv <- newTVar cs
  exit $ Column dt clv csv

growColumn :: EdhThreadState -> Int -> Column -> STM () -> STM ()
growColumn _ets !newCap (Column !dt !clv !csv) !exit = do
  !cl  <- takeTMVar clv
  !cs  <- readTVar csv
  !cs' <- flat'grow'array dt cs newCap
  writeTVar csv cs'
  putTMVar clv $ min newCap cl
  exit

unsafeReadColumnCell
  :: EdhThreadState -> Column -> Int -> (EdhValue -> STM ()) -> STM ()
unsafeReadColumnCell !ets (Column !dt _ !csv) !idx !exit =
  readTVar csv >>= \ !cs -> flat'array'read dt ets cs idx exit

unsafeWriteColumnCell
  :: EdhThreadState
  -> Column
  -> Int
  -> EdhValue
  -> (EdhValue -> STM ())
  -> STM ()
unsafeWriteColumnCell !ets (Column !dt _ !csv) !idx !val !exit =
  readTVar csv >>= \ !cs -> flat'array'write dt ets cs idx val exit

unsafeFillColumn
  :: EdhThreadState -> Column -> EdhValue -> [Int] -> STM () -> STM ()
unsafeFillColumn !ets (Column !dt _ !csv) !val !idxs !exit =
  fromEdh ets val $ \ !sv -> readTVar csv
    >>= \ !cs -> flat'array'update dt ets [ (i, sv) | i <- idxs ] cs exit

unsafeSliceColumn :: Column -> Int -> Int -> Int -> (Column -> STM ()) -> STM ()
unsafeSliceColumn (Column !dt !clv (csv :: TVar FlatArray)) !start !stop !step !exit
  = do
    !cl <- readTMVar clv
    readTVar csv >>= \case
      cs@(DeviceArray !cap (fp :: ForeignPtr a)) ->
        if start >= cap || stop == start
          then do
            !clv' <- newTMVar 0
            !csv' <- newTVar (emptyDeviceArray @a)
            exit $ Column dt clv' csv'
          else if step == 1
            then do
              let !len = max 0 $ min cl stop - start
                  !cs' = unsafeSliceFlatArray cs start (cap - start)
              !clv' <- newTMVar len
              !csv' <- newTVar cs'
              exit $ Column dt clv' csv'
            else do
              let (q, r) = quotRem (stop - start) step
                  !len   = if r == 0 then abs q else 1 + abs q
              !fp' <- unsafeIOToSTM $ withForeignPtr fp $ \ !p -> do
                !p'  <- callocArray len
                !fp' <- newForeignPtr finalizerFree p'
                let fillRng :: Int -> Int -> IO ()
                    fillRng !n !i = if i >= len
                      then return ()
                      else do
                        peekElemOff p n >>= pokeElemOff p' i
                        fillRng (n + step) (i + 1)
                fillRng start 0
                return fp'
              let !cs' = DeviceArray len fp'
              !csv' <- newTVar cs'
              !clv' <- newTMVar len
              exit $ Column dt clv' csv'
      cs@(HostArray !cap (ha :: MV.IOVector a)) ->
        if start >= cap || stop == start
          then do
            !clv' <- newTMVar 0
            !csv' <- newTVar (emptyHostArray @a)
            exit $ Column dt clv' csv'
          else if step == 1
            then do
              let !len = max 0 $ min cl stop - start
                  !cs' = unsafeSliceFlatArray cs start (cap - start)
              !clv' <- newTMVar len
              !csv' <- newTVar cs'
              exit $ Column dt clv' csv'
            else do
              let (q, r) = quotRem (stop - start) step
                  !len   = if r == 0 then abs q else 1 + abs q
              !ha' <- unsafeIOToSTM $ do
                !ha' <- MV.unsafeNew len
                let fillRng :: Int -> Int -> IO ()
                    fillRng !n !i = if i >= len
                      then return ()
                      else do
                        MV.unsafeRead ha n >>= MV.unsafeWrite ha' i
                        fillRng (n + step) (i + 1)
                fillRng start 0
                return ha'
              let !cs' = HostArray len ha'
              !csv' <- newTVar cs'
              !clv' <- newTMVar len
              exit $ Column dt clv' csv'


extractColumnBool
  :: EdhThreadState
  -> Column
  -> Column
  -> STM ()
  -> (Column -> STM ())
  -> STM ()
extractColumnBool !ets (Column _mdt !mclv !mcsv) (Column !dt !clv !csv) !naExit !exit
  = do
    !cl <- readTMVar clv
    !cs <- readTVar csv
    resolveDataOperator' ets (data'type'identifier dt) cs naExit $ \ !dtOp -> do
      let !fa = unsafeSliceFlatArray cs 0 cl
      !mcl <- readTMVar mclv
      if mcl /= cl
        then
          throwEdh ets UsageError
          $  "index length mismatch: "
          <> T.pack (show mcl)
          <> " vs "
          <> T.pack (show cl)
        else do
          !mcs <- readTVar mcsv
          let !ma = unsafeSliceFlatArray mcs 0 mcl
          flat'extract'yesno dtOp ets ma fa $ \(!rfa, !rlen) -> do
            !clvRtn <- newTMVar rlen
            !csvRtn <- newTVar rfa
            exit $ Column dt clvRtn csvRtn


extractColumnFancy
  :: EdhThreadState
  -> Column
  -> Column
  -> STM ()
  -> (Column -> STM ())
  -> STM ()
extractColumnFancy !ets (Column _idti !iclv !icsv) (Column !dt !clv !csv) !naExit !exit
  = do
    !icl <- readTMVar iclv
    !ics <- readTVar icsv
    !cl  <- readTMVar clv
    !cs  <- readTVar csv
    resolveDataOperator' ets (data'type'identifier dt) cs naExit $ \ !dtOp -> do
      let !ifa = unsafeSliceFlatArray ics 0 icl
          !fa  = unsafeSliceFlatArray cs 0 cl
      flat'extract'fancy dtOp ets ifa fa $ \ !rfa -> do
        !clvRtn <- newTMVar icl
        !csvRtn <- newTVar rfa
        exit $ Column dt clvRtn csvRtn


vecCmpColumn
  :: DataType
  -> EdhThreadState
  -> (Ordering -> Bool)
  -> Column
  -> EdhValue
  -> (Column -> STM ())
  -> STM ()
vecCmpColumn !dtYesNo !ets !cmp (Column !dt !clv !csv) !v !exit = do
  !cl <- readTMVar clv
  !cs <- readTVar csv
  resolveDataComparator ets (data'type'identifier dt) cs $ \ !dtOrd -> do
    let !fa = unsafeSliceFlatArray cs 0 cl
    flat'cmp'vectorized dtOrd ets fa cmp v $ \ !bifa -> do
      !biclv <- newTMVar cl
      !bicsv <- newTVar bifa
      exit $ Column dtYesNo biclv bicsv

elemCmpColumn
  :: DataType
  -> EdhThreadState
  -> (Ordering -> Bool)
  -> Column
  -> Column
  -> (Column -> STM ())
  -> STM ()
elemCmpColumn !dtYesNo !ets !cmp (Column !dt1 !clv1 !csv1) (Column !dt2 !clv2 !csv2) !exit
  = if data'type'identifier dt1 /= data'type'identifier dt2
    then
      throwEdh ets UsageError
      $  "column dtype mismatch: "
      <> (data'type'identifier dt1)
      <> " vs "
      <> (data'type'identifier dt2)
    else do
      !cl1 <- readTMVar clv1
      !cl2 <- readTMVar clv2
      if cl1 /= cl2
        then
          throwEdh ets UsageError
          $  "column length mismatch: "
          <> T.pack (show cl1)
          <> " vs "
          <> T.pack (show cl2)
        else do
          !cs1 <- readTVar csv1
          !cs2 <- readTVar csv2
          resolveDataComparator ets (data'type'identifier dt1) cs1
            $ \ !dtOrd -> do
                let !fa1 = unsafeSliceFlatArray cs1 0 cl1
                    !fa2 = unsafeSliceFlatArray cs2 0 cl2
                flat'cmp'element'wise dtOrd ets fa1 cmp fa2 $ \ !bifa -> do
                  !biclv <- newTMVar cl1
                  !bicsv <- newTVar bifa
                  exit $ Column dtYesNo biclv bicsv

vecOpColumn
  :: EdhThreadState
  -> (Text -> Dynamic)
  -> Column
  -> EdhValue
  -> STM ()
  -> (Column -> STM ())
  -> STM ()
vecOpColumn !ets !getOp (Column !dt !clv !csv) !v !naExit !exit = do
  !cl <- readTMVar clv
  !cs <- readTVar csv
  resolveDataOperator' ets (data'type'identifier dt) cs naExit $ \ !dtOp -> do
    let !fa  = unsafeSliceFlatArray cs 0 cl
    let !dop = getOp (data'type'identifier dt)
    case fromDynamic dop of
      Just EdhNil -> naExit
      _           -> flat'op'vectorized dtOp ets fa dop v $ \ !bifa -> do
        !biclv <- newTMVar cl
        !bicsv <- newTVar bifa
        exit $ Column dt biclv bicsv

elemOpColumn
  :: EdhThreadState
  -> (Text -> Dynamic)
  -> Column
  -> Column
  -> STM ()
  -> (Column -> STM ())
  -> STM ()
elemOpColumn !ets !getOp (Column !dt1 !clv1 !csv1) (Column !dt2 !clv2 !csv2) !naExit !exit
  = if data'type'identifier dt1 /= data'type'identifier dt2
    then
      throwEdh ets UsageError
      $  "column dtype mismatch: "
      <> (data'type'identifier dt1)
      <> " vs "
      <> (data'type'identifier dt2)
    else do
      !cl1 <- readTMVar clv1
      !cl2 <- readTMVar clv2
      if cl1 /= cl2
        then
          throwEdh ets UsageError
          $  "column length mismatch: "
          <> T.pack (show cl1)
          <> " vs "
          <> T.pack (show cl2)
        else do
          !cs1 <- readTVar csv1
          !cs2 <- readTVar csv2
          resolveDataOperator' ets (data'type'identifier dt1) cs1 naExit
            $ \ !dtOp -> do
                let !fa1 = unsafeSliceFlatArray cs1 0 cl1
                    !fa2 = unsafeSliceFlatArray cs2 0 cl2
                let !dop = getOp (data'type'identifier dt1)
                case fromDynamic dop of
                  Just EdhNil -> naExit
                  _ -> flat'op'element'wise dtOp ets fa1 dop fa2 $ \ !bifa ->
                    do
                      !biclv <- newTMVar cl1
                      !bicsv <- newTVar bifa
                      exit $ Column dt1 biclv bicsv

vecInpColumn
  :: EdhThreadState
  -> (Text -> Dynamic)
  -> Column
  -> EdhValue
  -> STM ()
  -> STM ()
  -> STM ()
vecInpColumn !ets !getOp (Column !dt !clv !csv) !v !naExit !exit = do
  !cl <- readTMVar clv
  !cs <- readTVar csv
  resolveDataOperator' ets (data'type'identifier dt) cs naExit $ \ !dtOp -> do
    let !fa  = unsafeSliceFlatArray cs 0 cl
    let !dop = getOp (data'type'identifier dt)
    case fromDynamic dop of
      Just EdhNil -> naExit
      _           -> flat'inp'vectorized dtOp ets fa dop v exit

vecInpSliceColumn
  :: EdhThreadState
  -> (Int, Int, Int)
  -> (Text -> Dynamic)
  -> Column
  -> EdhValue
  -> STM ()
  -> STM ()
  -> STM ()
vecInpSliceColumn !ets !slice !getOp (Column !dt !clv !csv) !v !naExit !exit =
  do
    !cl <- readTMVar clv
    !cs <- readTVar csv
    resolveDataOperator' ets (data'type'identifier dt) cs naExit $ \ !dtOp -> do
      let !fa  = unsafeSliceFlatArray cs 0 cl
      let !dop = getOp (data'type'identifier dt)
      case fromDynamic dop of
        Just EdhNil -> naExit
        _           -> flat'inp'vectorized'slice dtOp ets slice fa dop v exit

vecInpMaskedColumn
  :: EdhThreadState
  -> Column
  -> (Text -> Dynamic)
  -> Column
  -> EdhValue
  -> STM ()
  -> STM ()
  -> STM ()
vecInpMaskedColumn !ets (Column _ !mclv !mcsv) !getOp (Column !dt !clv !csv) !v !naExit !exit
  = do
    !cl <- readTMVar clv
    !cs <- readTVar csv
    resolveDataOperator' ets (data'type'identifier dt) cs naExit $ \ !dtOp -> do
      let !fa  = unsafeSliceFlatArray cs 0 cl
      let !dop = getOp (data'type'identifier dt)
      case fromDynamic dop of
        Just EdhNil -> naExit
        _           -> do
          !mcl <- readTMVar mclv
          if mcl /= cl
            then
              throwEdh ets UsageError
              $  "index length mismatch: "
              <> T.pack (show mcl)
              <> " vs "
              <> T.pack (show cl)
            else do
              !mcs <- readTVar mcsv
              let !ma = unsafeSliceFlatArray mcs 0 mcl
              flat'inp'vectorized'masked dtOp ets ma fa dop v exit

vecInpFancyColumn
  :: EdhThreadState
  -> Column
  -> (Text -> Dynamic)
  -> Column
  -> EdhValue
  -> STM ()
  -> STM ()
  -> STM ()
vecInpFancyColumn !ets (Column _ !iclv !icsv) !getOp (Column !dt !clv !csv) !v !naExit !exit
  = do
    !cl <- readTMVar clv
    !cs <- readTVar csv
    resolveDataOperator' ets (data'type'identifier dt) cs naExit $ \ !dtOp -> do
      let !fa  = unsafeSliceFlatArray cs 0 cl
      let !dop = getOp (data'type'identifier dt)
      case fromDynamic dop of
        Just EdhNil -> naExit
        _           -> do
          !icl <- readTMVar iclv
          !ics <- readTVar icsv
          let !ia = unsafeSliceFlatArray ics 0 icl
          flat'inp'vectorized'fancy dtOp ets ia fa dop v exit

elemInpColumn
  :: EdhThreadState
  -> (Text -> Dynamic)
  -> Column
  -> Column
  -> STM ()
  -> STM ()
  -> STM ()
elemInpColumn !ets !getOp (Column !dt1 !clv1 !csv1) (Column !dt2 !clv2 !csv2) !naExit !exit
  = if data'type'identifier dt1 /= data'type'identifier dt2
    then
      throwEdh ets UsageError
      $  "column dtype mismatch: "
      <> (data'type'identifier dt1)
      <> " vs "
      <> (data'type'identifier dt2)
    else do
      !cl1 <- readTMVar clv1
      !cl2 <- readTMVar clv2
      if cl1 /= cl2
        then
          throwEdh ets UsageError
          $  "column length mismatch: "
          <> T.pack (show cl1)
          <> " vs "
          <> T.pack (show cl2)
        else do
          !cs1 <- readTVar csv1
          !cs2 <- readTVar csv2
          resolveDataOperator' ets (data'type'identifier dt1) cs1 naExit
            $ \ !dtOp -> do
                let !fa1 = unsafeSliceFlatArray cs1 0 cl1
                    !fa2 = unsafeSliceFlatArray cs2 0 cl2
                let !dop = getOp (data'type'identifier dt1)
                case fromDynamic dop of
                  Just EdhNil -> naExit
                  _           -> flat'inp'element'wise dtOp ets fa1 dop fa2 exit

elemInpSliceColumn
  :: EdhThreadState
  -> (Int, Int, Int)
  -> (Text -> Dynamic)
  -> Column
  -> Column
  -> STM ()
  -> STM ()
  -> STM ()
elemInpSliceColumn !ets !slice !getOp (Column !dt1 !clv1 !csv1) (Column !dt2 !clv2 !csv2) !naExit !exit
  = if data'type'identifier dt1 /= data'type'identifier dt2
    then
      throwEdh ets UsageError
      $  "column dtype mismatch: "
      <> (data'type'identifier dt1)
      <> " vs "
      <> (data'type'identifier dt2)
    else do
      !cl1 <- readTMVar clv1
      !cl2 <- readTMVar clv2
      !cs1 <- readTVar csv1
      !cs2 <- readTVar csv2
      resolveDataOperator' ets (data'type'identifier dt1) cs1 naExit
        $ \ !dtOp -> do
            let !fa1 = unsafeSliceFlatArray cs1 0 cl1
                !fa2 = unsafeSliceFlatArray cs2 0 cl2
            let !dop = getOp (data'type'identifier dt1)
            case fromDynamic dop of
              Just EdhNil -> naExit
              _ -> flat'inp'element'wise'slice dtOp ets slice fa1 dop fa2 exit

elemInpMaskedColumn
  :: EdhThreadState
  -> Column
  -> (Text -> Dynamic)
  -> Column
  -> Column
  -> STM ()
  -> STM ()
  -> STM ()
elemInpMaskedColumn !ets (Column _ !mclv !mcsv) !getOp (Column !dt1 !clv1 !csv1) (Column !dt2 !clv2 !csv2) !naExit !exit
  = if data'type'identifier dt1 /= data'type'identifier dt2
    then
      throwEdh ets UsageError
      $  "column dtype mismatch: "
      <> (data'type'identifier dt1)
      <> " vs "
      <> (data'type'identifier dt2)
    else do
      !cl1 <- readTMVar clv1
      !cl2 <- readTMVar clv2
      if cl1 /= cl2
        then
          throwEdh ets UsageError
          $  "column length mismatch: "
          <> T.pack (show cl1)
          <> " vs "
          <> T.pack (show cl2)
        else do
          !mcl <- readTMVar mclv
          !mcs <- readTVar mcsv
          !cs1 <- readTVar csv1
          !cs2 <- readTVar csv2
          resolveDataOperator' ets (data'type'identifier dt1) cs1 naExit
            $ \ !dtOp -> do
                let !ma  = unsafeSliceFlatArray mcs 0 mcl
                    !fa1 = unsafeSliceFlatArray cs1 0 cl1
                    !fa2 = unsafeSliceFlatArray cs2 0 cl2
                let !dop = getOp (data'type'identifier dt1)
                case fromDynamic dop of
                  Just EdhNil -> naExit
                  _ ->
                    flat'inp'element'wise'masked dtOp ets ma fa1 dop fa2 exit

elemInpFancyColumn
  :: EdhThreadState
  -> Column
  -> (Text -> Dynamic)
  -> Column
  -> Column
  -> STM ()
  -> STM ()
  -> STM ()
elemInpFancyColumn !ets (Column _ !iclv !icsv) !getOp (Column !dt1 !clv1 !csv1) (Column !dt2 !clv2 !csv2) !naExit !exit
  = if data'type'identifier dt1 /= data'type'identifier dt2
    then
      throwEdh ets UsageError
      $  "column dtype mismatch: "
      <> (data'type'identifier dt1)
      <> " vs "
      <> (data'type'identifier dt2)
    else do
      !cl1 <- readTMVar clv1
      !cl2 <- readTMVar clv2
      if cl1 /= cl2
        then
          throwEdh ets UsageError
          $  "column length mismatch: "
          <> T.pack (show cl1)
          <> " vs "
          <> T.pack (show cl2)
        else do
          !icl <- readTMVar iclv
          !ics <- readTVar icsv
          !cs1 <- readTVar csv1
          !cs2 <- readTVar csv2
          resolveDataOperator' ets (data'type'identifier dt1) cs1 naExit
            $ \ !dtOp -> do
                let !ia  = unsafeSliceFlatArray ics 0 icl
                    !fa1 = unsafeSliceFlatArray cs1 0 cl1
                    !fa2 = unsafeSliceFlatArray cs2 0 cl2
                let !dop = getOp (data'type'identifier dt1)
                case fromDynamic dop of
                  Just EdhNil -> naExit
                  _ -> flat'inp'element'wise'fancy dtOp ets ia fa1 dop fa2 exit


nonzeroIdxColumn :: EdhThreadState -> Column -> (Column -> STM ()) -> STM ()
nonzeroIdxColumn !ets (Column _mdti !mclv !mcsv) !exit =
  resolveNumDataType ets (data'type'identifier dtIntp) $ \ !ndt -> do
    !mcl <- readTMVar mclv
    !mcs <- readTVar mcsv
    let !ma = unsafeSliceFlatArray mcs 0 mcl
    flat'new'nonzero'array ndt ets ma $ \(!rfa, !rlen) -> do
      !clvRtn <- newTMVar rlen
      !csvRtn <- newTVar rfa
      exit $ Column dtIntp clvRtn csvRtn
  where dtIntp = makeDeviceDataType @Int "intp"


-- obtain valid column data as an immutable Storable Vector
-- this is unsafe in both memory/type regards and thread regards
unsafeCastColumnData
  :: forall a
   . (Storable a, EdhXchg a, Typeable a)
  => Column
  -> STM (VS.Vector a)
unsafeCastColumnData (Column _ _ !csv) = do
  !ary <- readTVar csv
  return $ unsafeFlatArrayAsVector ary

-- obtain valid column data as a mutable Storable Vector
-- this is unsafe in both memory/type regards and thread regards
unsafeCastMutableColumnData
  :: forall a
   . (Storable a, EdhXchg a, Typeable a)
  => Column
  -> STM (MVS.IOVector a)
unsafeCastMutableColumnData (Column _ _ !csv) = do
  !ary <- readTVar csv
  return $ unsafeFlatArrayAsMVector ary


createColumnClass :: Object -> Scope -> STM Object
createColumnClass !defaultDt !clsOuterScope =
  mkHostClass clsOuterScope "Column" (allocEdhObj columnAllocator) []
    $ \ !clsScope -> do
        !mths <-
          sequence
          $  [ (AttrByName nm, ) <$> mkHostProc clsScope vc nm hp
             | (nm, vc, hp) <-
               [ ("__cap__" , EdhMethod, wrapHostProc colCapProc)
               , ("__grow__", EdhMethod, wrapHostProc colGrowProc)
               , ("__len__" , EdhMethod, wrapHostProc colLenProc)
               , ("__mark__", EdhMethod, wrapHostProc colMarkLenProc)
               , ("[]"      , EdhMethod, wrapHostProc colIdxReadProc)
               , ("[=]"     , EdhMethod, wrapHostProc colIdxWriteProc)
               , ("__repr__", EdhMethod, wrapHostProc colReprProc)
               , ("__show__", EdhMethod, wrapHostProc colShowProc)
               , ("__desc__", EdhMethod, wrapHostProc colDescProc)
               , ( "=="
                 , EdhMethod
                 , wrapHostProc $ colCmpProc $ \case
                   EQ -> True
                   _  -> False
                 )
               , ( "==@"
                 , EdhMethod
                 , wrapHostProc $ colCmpProc $ \case
                   EQ -> True
                   _  -> False
                 )
               , ( "!="
                 , EdhMethod
                 , wrapHostProc $ colCmpProc $ \case
                   EQ -> False
                   _  -> True
                 )
               , ( "!=@"
                 , EdhMethod
                 , wrapHostProc $ colCmpProc $ \case
                   EQ -> False
                   _  -> True
                 )
               , ( ">="
                 , EdhMethod
                 , wrapHostProc $ colCmpProc $ \case
                   GT -> True
                   EQ -> True
                   _  -> False
                 )
               , ( "<="
                 , EdhMethod
                 , wrapHostProc $ colCmpProc $ \case
                   LT -> True
                   EQ -> True
                   _  -> False
                 )
               , ( "<"
                 , EdhMethod
                 , wrapHostProc $ colCmpProc $ \case
                   LT -> True
                   _  -> False
                 )
               , ( ">"
                 , EdhMethod
                 , wrapHostProc $ colCmpProc $ \case
                   GT -> True
                   _  -> False
                 )
               , ( ">=@"
                 , EdhMethod
                 , wrapHostProc $ colCmpProc $ \case
                   LT -> True
                   EQ -> True
                   _  -> False
                 )
               , ( "<=@"
                 , EdhMethod
                 , wrapHostProc $ colCmpProc $ \case
                   GT -> True
                   EQ -> True
                   _  -> False
                 )
               , ( "<@"
                 , EdhMethod
                 , wrapHostProc $ colCmpProc $ \case
                   GT -> True
                   _  -> False
                 )
               , ( ">@"
                 , EdhMethod
                 , wrapHostProc $ colCmpProc $ \case
                   LT -> True
                   _  -> False
                 )
               , ("&&" , EdhMethod, wrapHostProc $ colOpProc bitAndOp)
               , ("&&@", EdhMethod, wrapHostProc $ colOpProc bitAndOp)
               , ("||" , EdhMethod, wrapHostProc $ colOpProc bitOrOp)
               , ("||@", EdhMethod, wrapHostProc $ colOpProc bitOrOp)
               , ("&&=", EdhMethod, wrapHostProc $ colInpProc bitAndOp)
               , ("||=", EdhMethod, wrapHostProc $ colInpProc bitOrOp)
               , ("+"  , EdhMethod, wrapHostProc $ colOpProc addOp)
               , ("+@" , EdhMethod, wrapHostProc $ colOpProc addOp)
               , ("+=" , EdhMethod, wrapHostProc $ colInpProc addOp)
               , ("-"  , EdhMethod, wrapHostProc $ colOpProc subtractOp)
               , ("-@" , EdhMethod, wrapHostProc $ colOpProc subtFromOp)
               , ("-=" , EdhMethod, wrapHostProc $ colInpProc subtractOp)
               , ("*"  , EdhMethod, wrapHostProc $ colOpProc mulOp)
               , ("*@" , EdhMethod, wrapHostProc $ colOpProc mulOp)
               , ("*=" , EdhMethod, wrapHostProc $ colInpProc mulOp)
               , ("/"  , EdhMethod, wrapHostProc $ colOpProc divOp)
               , ("/@" , EdhMethod, wrapHostProc $ colOpProc divByOp)
               , ("/=" , EdhMethod, wrapHostProc $ colInpProc divOp)
               , ("//" , EdhMethod, wrapHostProc $ colOpProc divIntOp)
               , ("//@", EdhMethod, wrapHostProc $ colOpProc divIntByOp)
               , ("//=", EdhMethod, wrapHostProc $ colInpProc divIntOp)
               , ("**" , EdhMethod, wrapHostProc $ colOpProc powOp)
               , ("**@", EdhMethod, wrapHostProc $ colOpProc powToOp)
               , ("**=", EdhMethod, wrapHostProc $ colInpProc powOp)
               ]
             ]
          ++ [ (AttrByName nm, ) <$> mkHostProperty clsScope nm getter setter
             | (nm, getter, setter) <- [("dtype", colDtypeProc, Nothing)]
             ]
        iopdUpdate mths $ edh'scope'entity clsScope

 where

  -- | host constructor Column(capacity, length=None, dtype=float64)
  columnAllocator
    :: "capacity" !: Int
    -> "length" ?: Int
    -> "dtype" ?: Object
    -> ArgsPack -- allow/ignore arbitrary ctor args for descendant classes
    -> EdhObjectAllocator
  columnAllocator (mandatoryArg -> !ctorCap) (defaultArg ctorCap -> !ctorLen) (defaultArg defaultDt -> dto) _ctorOtherArgs !ctorExit !etsCtor
    | ctorCap <= 0
    = throwEdh etsCtor UsageError
      $  "column capacity should be a positive interger, not "
      <> T.pack (show ctorCap)
    | ctorLen < 0
    = throwEdh etsCtor UsageError
      $  "column length should be zero or a positive integer, not "
      <> T.pack (show ctorLen)
    | otherwise
    = castObjectStore dto >>= \case
      Nothing       -> throwEdh etsCtor UsageError "invalid dtype"
      Just (_, !dt) -> do
        !lv <- newTMVar ctorLen
        createColumn etsCtor
                     dt
                     ctorCap
                     lv
                     ((ctorExit . HostStore =<<) . newTVar . toDyn)

  dtYesNo = makeDeviceDataType @YesNo "yesno"

  colGrowProc :: "newCap" !: Int -> EdhHostProc
  colGrowProc (mandatoryArg -> !newCap) !exit !ets = if newCap < 0
    then throwEdh ets UsageError $ "invalid newCap: " <> T.pack (show newCap)
    else withThisHostObj ets $ \_hsv !col ->
      growColumn ets newCap col
        $ exitEdh ets exit
        $ EdhObject
        $ edh'scope'that
        $ contextScope
        $ edh'context ets

  colCapProc :: EdhHostProc
  colCapProc !exit !ets = withThisHostObj ets $ \_hsv !col ->
    columnCapacity col
      >>= \ !cap -> exitEdh ets exit $ EdhDecimal $ fromIntegral cap

  colLenProc :: EdhHostProc
  colLenProc !exit !ets = withThisHostObj ets $ \_hsv !col -> columnLength col
    >>= \ !len -> exitEdh ets exit $ EdhDecimal $ fromIntegral len

  colMarkLenProc :: "newLen" !: Int -> EdhHostProc
  colMarkLenProc (mandatoryArg -> !newLen) !exit !ets =
    withThisHostObj ets $ \_hsv !col -> do
      !cap <- columnCapacity col
      if newLen >= 0 && newLen <= fromIntegral cap
        then unsafeMarkColumnLength newLen col >> exitEdh ets exit nil
        else throwEdh ets UsageError "column length out of range"

  colDtypeProc :: EdhHostProc
  colDtypeProc !exit !ets = withThisHostObj ets $ \_hsv (Column !dt _ _) ->
    exitEdh ets exit $ EdhString $ data'type'identifier dt

  colReprProc :: EdhHostProc
  colReprProc !exit !ets =
    withThisHostObj' ets (exitEdh ets exit $ EdhString "<bogus-Column>")
      $ \_hsv (Column !dt !clv !csv) -> do
          !cl <- readTMVar clv
          !cs <- readTVar csv
          exitEdh ets exit
            $  EdhString
            $  "Column( capacity="
            <> T.pack (show $ flatArrayCapacity cs)
            <> ", length="
            <> T.pack (show cl)
            <> ", dtype="
            <> (data'type'identifier dt) -- assuming the identifier is available as attr
            <> ")"

  colShowProc :: EdhHostProc
  colShowProc !exit !ets =
    withThisHostObj ets $ \_hsv (Column !dt !clv !csv) -> do
      !cl <- readTMVar clv
      !cs <- readTVar csv
      showData cl $ flat'array'read dt ets cs
   where
    !thisCol = edh'scope'this $ contextScope $ edh'context ets

    exitWithDetails :: Text -> STM ()
    exitWithDetails !details = edhValueRepr ets (EdhObject thisCol)
      $ \ !repr -> exitEdh ets exit $ EdhString $ repr <> "\n" <> details

    showData :: Int -> (Int -> (EdhValue -> STM ()) -> STM ()) -> STM ()
    showData !len !readElem = go 0 [] 0 ""
     where
      go :: Int -> [Text] -> Int -> Text -> STM ()
      -- TODO don't generate all lines for large columns
      go !i !cumLines !lineIdx !line | i >= len =
        exitWithDetails $ if T.null line && null cumLines
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
        edhValueRepr ets elemVal $ \ !elemRepr ->
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
  colDescProc :: EdhHostProc
  colDescProc !exit =
    exitEdhTx exit
      $  EdhString
      $  " * Statistical Description of Column data,\n"
      <> "   like pandas describe(), is yet to be implemented."


  colIdxReadProc :: EdhValue -> EdhHostProc
  colIdxReadProc !idxVal !exit !ets = withThisHostObj ets $ \_hsv !col ->
    castObjectStore' idxVal >>= \case
      Just (_, !idxCol) ->
        case data'type'identifier $ column'data'type idxCol of
          "yesno" -> -- yesno index 
                     extractColumnBool ets
                                       idxCol
                                       col
                                       (exitEdh ets exit edhNA)
                                       exitWithNewClone
          "intp" -> -- fancy index 
                    extractColumnFancy ets
                                       idxCol
                                       col
                                       (exitEdh ets exit edhNA)
                                       exitWithNewClone
          !badDti ->
            throwEdh ets UsageError
              $  "invalid dtype="
              <> badDti
              <> " for a column as an index to another column"
      Nothing -> parseEdhIndex ets idxVal $ \case
        Left !err -> throwEdh ets UsageError err
        Right (EdhIndex !i) ->
          unsafeReadColumnCell ets col i $ exitEdh ets exit
        Right EdhAny -> exitEdh ets exit $ EdhObject thatCol
        Right EdhAll -> exitEdh ets exit $ EdhObject thatCol
        Right (EdhSlice !start !stop !step) -> do
          !cl <- columnLength col
          edhRegulateSlice ets cl (start, stop, step)
            $ \(!iStart, !iStop, !iStep) ->
                unsafeSliceColumn col iStart iStop iStep exitWithNewClone
   where
    !thisCol = edh'scope'this $ contextScope $ edh'context ets
    !thatCol = edh'scope'that $ contextScope $ edh'context ets
    exitWithNewClone !colResult = edhCloneHostObj ets thisCol thatCol colResult
      $ \ !newColObj -> exitEdh ets exit $ EdhObject newColObj

  colIdxWriteProc :: EdhValue -> EdhValue -> EdhHostProc
  colIdxWriteProc !idxVal !other !exit !ets =
    withThisHostObj ets $ \_hsv col@(Column !dt !clv _csv) ->
      castObjectStore' (edhUltimate other) >>= \case
        -- assign column to column
        Just (_, colOther@(Column !dtOther !clvOther _)) -> if dtOther /= dt
          then
            throwEdh ets UsageError
            $  "assigning column of dtype="
            <> (data'type'identifier dtOther)
            <> " to dtype="
            <> (data'type'identifier dt)
            <> " not supported."
          else castObjectStore' idxVal >>= \case
            Just (_, !idxCol) ->
              case data'type'identifier $ column'data'type idxCol of
                "yesno" -> -- yesno index
                  elemInpMaskedColumn ets
                                      idxCol
                                      assignOp
                                      col
                                      colOther
                                      (exitEdh ets exit edhNA)
                    $ exitEdh ets exit
                    $ EdhObject thatCol
                "intp" -> -- fancy index
                  elemInpFancyColumn ets
                                     idxCol
                                     assignOp
                                     col
                                     colOther
                                     (exitEdh ets exit edhNA)
                    $ exitEdh ets exit
                    $ EdhObject thatCol
                !badDti ->
                  throwEdh ets UsageError
                    $  "invalid dtype="
                    <> badDti
                    <> " for a column as an index to another column"
            Nothing -> parseEdhIndex ets idxVal $ \case
              Left  !err         -> throwEdh ets UsageError err
              Right (EdhIndex _) -> throwEdh
                ets
                UsageError
                "can not assign a column to a single index of another column"
              Right EdhAny -> throwEdh
                ets
                UsageError
                "can not assign a column to every element of another column"
              Right EdhAll -> if dtOther /= dt
                then
                  throwEdh ets UsageError
                  $  "assigning column of dtype="
                  <> (data'type'identifier dtOther)
                  <> " to "
                  <> (data'type'identifier dt)
                  <> " not supported."
                else do
                  !cl      <- readTMVar clv
                  !clOther <- readTMVar clvOther
                  if clOther /= cl
                    then
                      throwEdh ets UsageError
                      $  "column length mismatch: "
                      <> T.pack (show clOther)
                      <> " vs "
                      <> T.pack (show cl)
                    else
                      elemInpColumn ets
                                    assignOp
                                    col
                                    colOther
                                    (exitEdh ets exit edhNA)
                      $ exitEdh ets exit
                      $ EdhObject thatCol
              Right (EdhSlice !start !stop !step) -> do
                !cl <- columnLength col
                edhRegulateSlice ets cl (start, stop, step) $ \ !slice ->
                  elemInpSliceColumn ets
                                     slice
                                     assignOp
                                     col
                                     colOther
                                     (exitEdh ets exit edhNA)
                    $ exitEdh ets exit other

        -- assign scalar to column
        Nothing -> castObjectStore' idxVal >>= \case
          Just (_, idxCol@(Column !dtIdx _clvIdx _csvIdx)) ->
            case data'type'identifier dtIdx of
              "yesno" -> -- yesno index
                vecInpMaskedColumn ets
                                   idxCol
                                   assignOp
                                   col
                                   (edhUltimate other)
                                   (exitEdh ets exit edhNA)
                  $ exitEdh ets exit
                  $ EdhObject thatCol
              "intp" -> -- fancy index
                vecInpFancyColumn ets
                                  idxCol
                                  assignOp
                                  col
                                  (edhUltimate other)
                                  (exitEdh ets exit edhNA)
                  $ exitEdh ets exit
                  $ EdhObject thatCol
              !badDti ->
                throwEdh ets UsageError
                  $  "invalid dtype="
                  <> badDti
                  <> " for a column as an index to another column"
          Nothing -> parseEdhIndex ets idxVal $ \case
            Left !err -> throwEdh ets UsageError err
            Right (EdhIndex !i) ->
              unsafeWriteColumnCell ets col i (edhUltimate other)
                $ exitEdh ets exit
            Right EdhAny -> do
              !cl <- columnLength col
              unsafeFillColumn ets col (edhUltimate other) [0 .. cl - 1]
                $ exitEdh ets exit
                $ EdhObject thatCol
            Right EdhAll -> do
              !cl <- columnLength col
              unsafeFillColumn ets col (edhUltimate other) [0 .. cl - 1]
                $ exitEdh ets exit
                $ EdhObject thatCol
            Right (EdhSlice !start !stop !step) -> do
              !cl <- columnLength col
              edhRegulateSlice ets cl (start, stop, step)
                $ \(!iStart, !iStop, !iStep) ->
                    vecInpSliceColumn ets
                                      (iStart, iStop, iStep)
                                      assignOp
                                      col
                                      (edhUltimate other)
                                      (exitEdh ets exit edhNA)
                      $ exitEdh ets exit
                      $ EdhObject thatCol
    where thatCol = edh'scope'that $ contextScope $ edh'context ets


  colCmpProc :: (Ordering -> Bool) -> EdhValue -> EdhHostProc
  colCmpProc !cmp !other !exit !ets = withThisHostObj ets $ \_hsv !col ->
    let !otherVal = edhUltimate other
    in  castObjectStore' otherVal >>= \case
          Just (_, colOther@Column{}) ->
            elemCmpColumn dtYesNo ets cmp col colOther exitWithResult
          _ -> vecCmpColumn dtYesNo ets cmp col otherVal exitWithResult
   where
    !thisCol = edh'scope'this $ contextScope $ edh'context ets
    exitWithResult !colResult =
      edhCreateHostObj (edh'obj'class thisCol) (toDyn colResult) []
        >>= exitEdh ets exit
        .   EdhObject


  colOpProc :: (Text -> Dynamic) -> EdhValue -> EdhHostProc
  colOpProc !getOp !other !exit !ets = withThisHostObj ets $ \_hsv !col ->
    let !otherVal = edhUltimate other
    in  castObjectStore' otherVal >>= \case
          Just (_, colOther@Column{}) -> elemOpColumn
            ets
            getOp
            col
            colOther
            (exitEdh ets exit edhNA)
            exitWithNewClone
          _ -> vecOpColumn ets
                           getOp
                           col
                           otherVal
                           (exitEdh ets exit edhNA)
                           exitWithNewClone
   where
    !thisCol = edh'scope'this $ contextScope $ edh'context ets
    !thatCol = edh'scope'that $ contextScope $ edh'context ets
    exitWithNewClone !colResult = edhCloneHostObj ets thisCol thatCol colResult
      $ \ !newColObj -> exitEdh ets exit $ EdhObject newColObj

  colInpProc :: (Text -> Dynamic) -> EdhValue -> EdhHostProc
  colInpProc !getOp !other !exit !ets = withThisHostObj ets $ \_hsv !col ->
    let !otherVal = edhUltimate other
    in  castObjectStore' otherVal >>= \case
          Just (_, colOther@Column{}) ->
            elemInpColumn ets getOp col colOther (exitEdh ets exit edhNA)
              $ exitEdh ets exit
              $ EdhObject thatCol
          _ ->
            vecInpColumn ets getOp col otherVal (exitEdh ets exit edhNA)
              $ exitEdh ets exit
              $ EdhObject thatCol
    where !thatCol = edh'scope'that $ contextScope $ edh'context ets

  assignOp :: Text -> Dynamic
  assignOp = \case
    "float64" -> toDyn ((\_x !y -> y) :: Double -> Double -> Double)
    "float32" -> toDyn ((\_x !y -> y) :: Float -> Float -> Float)
    "int64"   -> toDyn ((\_x !y -> y) :: Int64 -> Int64 -> Int64)
    "int32"   -> toDyn ((\_x !y -> y) :: Int32 -> Int32 -> Int32)
    "int8"    -> toDyn ((\_x !y -> y) :: Int8 -> Int8 -> Int8)
    "byte"    -> toDyn ((\_x !y -> y) :: Word8 -> Word8 -> Word8)
    "intp"    -> toDyn ((\_x !y -> y) :: Int -> Int -> Int)
    "yesno"   -> toDyn ((\_x !y -> y) :: YesNo -> YesNo -> YesNo)
    "decimal" -> toDyn ((\_x !y -> y) :: D.Decimal -> D.Decimal -> D.Decimal)
    "box" ->
      let edhOp :: EdhValue -> EdhValue -> EdhHostProc
          edhOp _x !y !exit !ets = exitEdh ets exit y
      in  toDyn edhOp
    _ -> toDyn nil -- means not applicable here

  bitAndOp :: Text -> Dynamic
  bitAndOp = \case
    -- "float64" -> toDyn ((.&.) :: Double -> Double -> Double)
    -- "float32" -> toDyn ((.&.) :: Float -> Float -> Float)
    "int64" -> toDyn ((.&.) :: Int64 -> Int64 -> Int64)
    "int32" -> toDyn ((.&.) :: Int32 -> Int32 -> Int32)
    "int8"  -> toDyn ((.&.) :: Int8 -> Int8 -> Int8)
    "byte"  -> toDyn ((.&.) :: Word8 -> Word8 -> Word8)
    "intp"  -> toDyn ((.&.) :: Int -> Int -> Int)
    "yesno" -> toDyn ((.&.) :: YesNo -> YesNo -> YesNo)
    -- "decimal" -> toDyn ((.&.) :: D.Decimal -> D.Decimal -> D.Decimal)
    "box" ->
      let edhOp :: EdhValue -> EdhValue -> EdhHostProc
          edhOp !x !y =
              logicalAndProc (LitExpr $ ValueLiteral x) (LitExpr $ ValueLiteral y)
      in  toDyn edhOp
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
    "yesno" -> toDyn ((.|.) :: YesNo -> YesNo -> YesNo)
    -- "decimal" -> toDyn ((.|.) :: D.Decimal -> D.Decimal -> D.Decimal)
    "box" ->
      let edhOp :: EdhValue -> EdhValue -> EdhHostProc
          edhOp !x !y =
              logicalOrProc (LitExpr $ ValueLiteral x) (LitExpr $ ValueLiteral y)
      in  toDyn edhOp
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
    "decimal" -> toDyn ((+) :: D.Decimal -> D.Decimal -> D.Decimal)
    "box" ->
      let edhOp :: EdhValue -> EdhValue -> EdhHostProc
          edhOp !x !y =
              addProc (LitExpr $ ValueLiteral x) (LitExpr $ ValueLiteral y)
      in  toDyn edhOp
    _ -> toDyn nil -- means not applicable here
  subtractOp :: Text -> Dynamic
  subtractOp = \case
    "float64" -> toDyn ((-) :: Double -> Double -> Double)
    "float32" -> toDyn ((-) :: Float -> Float -> Float)
    "int64"   -> toDyn ((-) :: Int64 -> Int64 -> Int64)
    "int32"   -> toDyn ((-) :: Int32 -> Int32 -> Int32)
    "int8"    -> toDyn ((-) :: Int8 -> Int8 -> Int8)
    "byte"    -> toDyn ((-) :: Word8 -> Word8 -> Word8)
    "intp"    -> toDyn ((-) :: Int -> Int -> Int)
    "decimal" -> toDyn ((-) :: D.Decimal -> D.Decimal -> D.Decimal)
    "box" ->
      let edhOp :: EdhValue -> EdhValue -> EdhHostProc
          edhOp !x !y =
              subtProc (LitExpr $ ValueLiteral x) (LitExpr $ ValueLiteral y)
      in  toDyn edhOp
    _ -> toDyn nil -- means not applicable here
  subtFromOp :: Text -> Dynamic
  subtFromOp = \case
    "float64" -> toDyn ((\ !x !y -> y - x) :: Double -> Double -> Double)
    "float32" -> toDyn ((\ !x !y -> y - x) :: Float -> Float -> Float)
    "int64"   -> toDyn ((\ !x !y -> y - x) :: Int64 -> Int64 -> Int64)
    "int32"   -> toDyn ((\ !x !y -> y - x) :: Int32 -> Int32 -> Int32)
    "int8"    -> toDyn ((\ !x !y -> y - x) :: Int8 -> Int8 -> Int8)
    "byte"    -> toDyn ((\ !x !y -> y - x) :: Word8 -> Word8 -> Word8)
    "intp"    -> toDyn ((\ !x !y -> y - x) :: Int -> Int -> Int)
    "decimal" ->
      toDyn ((\ !x !y -> y - x) :: D.Decimal -> D.Decimal -> D.Decimal)
    "box" ->
      let edhOp :: EdhValue -> EdhValue -> EdhHostProc
          edhOp !x !y =
              subtProc (LitExpr $ ValueLiteral y) (LitExpr $ ValueLiteral x)
      in  toDyn edhOp
    _ -> toDyn nil -- means not applicable here
  mulOp :: Text -> Dynamic
  mulOp = \case
    "float64" -> toDyn ((*) :: Double -> Double -> Double)
    "float32" -> toDyn ((*) :: Float -> Float -> Float)
    "int64"   -> toDyn ((*) :: Int64 -> Int64 -> Int64)
    "int32"   -> toDyn ((*) :: Int32 -> Int32 -> Int32)
    "int8"    -> toDyn ((*) :: Int8 -> Int8 -> Int8)
    "byte"    -> toDyn ((*) :: Word8 -> Word8 -> Word8)
    "intp"    -> toDyn ((*) :: Int -> Int -> Int)
    "decimal" -> toDyn ((*) :: D.Decimal -> D.Decimal -> D.Decimal)
    "box" ->
      let edhOp :: EdhValue -> EdhValue -> EdhHostProc
          edhOp !x !y =
              mulProc (LitExpr $ ValueLiteral x) (LitExpr $ ValueLiteral y)
      in  toDyn edhOp
    _ -> toDyn nil -- means not applicable here
  divOp :: Text -> Dynamic
  divOp = \case
    "float64" -> toDyn ((/) :: Double -> Double -> Double)
    "float32" -> toDyn ((/) :: Float -> Float -> Float)
    "int64"   -> toDyn (div :: Int64 -> Int64 -> Int64)
    "int32"   -> toDyn (div :: Int32 -> Int32 -> Int32)
    "int8"    -> toDyn (div :: Int8 -> Int8 -> Int8)
    "byte"    -> toDyn (div :: Word8 -> Word8 -> Word8)
    "intp"    -> toDyn (div :: Int -> Int -> Int)
    "decimal" -> toDyn (D.divDecimal :: D.Decimal -> D.Decimal -> D.Decimal)
    "box" ->
      let edhOp :: EdhValue -> EdhValue -> EdhHostProc
          edhOp !x !y =
              divProc (LitExpr $ ValueLiteral x) (LitExpr $ ValueLiteral y)
      in  toDyn edhOp
    _ -> toDyn nil -- means not applicable here
  divByOp :: Text -> Dynamic
  divByOp = \case
    "float64" -> toDyn ((\ !x !y -> y / x) :: Double -> Double -> Double)
    "float32" -> toDyn ((\ !x !y -> y / x) :: Float -> Float -> Float)
    "int64"   -> toDyn ((\ !x !y -> div y x) :: Int64 -> Int64 -> Int64)
    "int32"   -> toDyn ((\ !x !y -> div y x) :: Int32 -> Int32 -> Int32)
    "int8"    -> toDyn ((\ !x !y -> div y x) :: Int8 -> Int8 -> Int8)
    "byte"    -> toDyn ((\ !x !y -> div y x) :: Word8 -> Word8 -> Word8)
    "intp"    -> toDyn ((\ !x !y -> div y x) :: Int -> Int -> Int)
    "decimal" -> toDyn
      ((\ !x !y -> D.divDecimal y x) :: D.Decimal -> D.Decimal -> D.Decimal)
    "box" ->
      let edhOp :: EdhValue -> EdhValue -> EdhHostProc
          edhOp !x !y =
              divProc (LitExpr $ ValueLiteral y) (LitExpr $ ValueLiteral x)
      in  toDyn edhOp
    _ -> toDyn nil -- means not applicable here
  divIntOp :: Text -> Dynamic
  divIntOp = \case
    -- TODO reason about this:
    -- https://stackoverflow.com/questions/38588815/rounding-errors-in-python-floor-division
    "float64" -> toDyn
      ((\ !x !y -> fromInteger $ floor $ x / y) :: Double -> Double -> Double)
    "float32" -> toDyn
      ((\ !x !y -> fromInteger $ floor $ x / y) :: Float -> Float -> Float)
    "int64"   -> toDyn (div :: Int64 -> Int64 -> Int64)
    "int32"   -> toDyn (div :: Int32 -> Int32 -> Int32)
    "int8"    -> toDyn (div :: Int8 -> Int8 -> Int8)
    "byte"    -> toDyn (div :: Word8 -> Word8 -> Word8)
    "intp"    -> toDyn (div :: Int -> Int -> Int)
    "decimal" -> toDyn (D.divIntDecimal :: D.Decimal -> D.Decimal -> D.Decimal)
    "box" ->
      let edhOp :: EdhValue -> EdhValue -> EdhHostProc
          edhOp !x !y =
              divIntProc (LitExpr $ ValueLiteral x) (LitExpr $ ValueLiteral y)
      in  toDyn edhOp
    _ -> toDyn nil -- means not applicable here
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
    "decimal" ->
      toDyn
        ((\ !x !y -> D.divIntDecimal y x) :: D.Decimal -> D.Decimal -> D.Decimal
        )
    "box" ->
      let edhOp :: EdhValue -> EdhValue -> EdhHostProc
          edhOp !x !y =
              divIntProc (LitExpr $ ValueLiteral y) (LitExpr $ ValueLiteral x)
      in  toDyn edhOp
    _ -> toDyn nil -- means not applicable here
  powOp :: Text -> Dynamic
  powOp = \case
    "float64" -> toDyn powerDouble
    "float32" -> toDyn powerFloat
    "int64"   -> toDyn ((^) :: Int64 -> Int64 -> Int64)
    "int32"   -> toDyn ((^) :: Int32 -> Int32 -> Int32)
    "int8"    -> toDyn ((^) :: Int8 -> Int8 -> Int8)
    "byte"    -> toDyn ((^) :: Word8 -> Word8 -> Word8)
    "intp"    -> toDyn ((^) :: Int -> Int -> Int)
    "decimal" -> toDyn D.powerDecimal
    "box" ->
      let edhOp :: EdhValue -> EdhValue -> EdhHostProc
          edhOp !x !y =
              powProc (LitExpr $ ValueLiteral x) (LitExpr $ ValueLiteral y)
      in  toDyn edhOp
    _ -> toDyn nil -- means not applicable here
  powToOp :: Text -> Dynamic
  powToOp = \case
    "float64" -> toDyn $ flip powerDouble
    "float32" -> toDyn $ flip powerFloat
    "int64"   -> toDyn $ flip ((^) :: Int64 -> Int64 -> Int64)
    "int32"   -> toDyn $ flip ((^) :: Int32 -> Int32 -> Int32)
    "int8"    -> toDyn $ flip ((^) :: Int8 -> Int8 -> Int8)
    "byte"    -> toDyn $ flip ((^) :: Word8 -> Word8 -> Word8)
    "intp"    -> toDyn $ flip ((^) :: Int -> Int -> Int)
    "decimal" -> toDyn $ flip D.powerDecimal
    "box" ->
      let edhOp :: EdhValue -> EdhValue -> EdhHostProc
          edhOp !x !y =
              powProc (LitExpr $ ValueLiteral y) (LitExpr $ ValueLiteral x)
      in  toDyn edhOp
    _ -> toDyn nil -- means not applicable here


arangeProc
  :: Object
  -> Object
  -> "rangeSpec" !: EdhValue
  -> "dtype" ?: Object
  -> EdhHostProc
arangeProc !defaultDt !colClass (mandatoryArg -> !rngSpec) (defaultArg defaultDt -> !dto) !exit !ets
  = castObjectStore dto >>= \case
    Nothing       -> throwEdh ets UsageError "invalid dtype"
    Just (_, !dt) -> case edhUltimate rngSpec of
      EdhPair (EdhPair (EdhDecimal !startN) (EdhDecimal !stopN)) (EdhDecimal stepN)
        -> case D.decimalToInteger startN of
          Just !start -> case D.decimalToInteger stopN of
            Just !stop -> case D.decimalToInteger stepN of
              Just !step -> createRangeCol dt
                                           (fromInteger start)
                                           (fromInteger stop)
                                           (fromInteger step)
              _ -> throwEdh ets UsageError "step is not an integer"
            _ -> throwEdh ets UsageError "stop is not an integer"
          _ -> throwEdh ets UsageError "start is not an integer"
      EdhPair (EdhDecimal !startN) (EdhDecimal !stopN) ->
        case D.decimalToInteger startN of
          Just !start -> case D.decimalToInteger stopN of
            Just !stop ->
              createRangeCol dt (fromInteger start) (fromInteger stop)
                $ if stop >= start then 1 else -1
            _ -> throwEdh ets UsageError "stop is not an integer"
          _ -> throwEdh ets UsageError "start is not an integer"
      EdhDecimal !stopN -> case D.decimalToInteger stopN of
        Just !stop ->
          createRangeCol dt 0 (fromInteger stop) $ if stop >= 0 then 1 else -1
        _ -> throwEdh ets UsageError "stop is not an integer"
      !badRngSpec -> edhValueRepr ets badRngSpec $ \ !rngRepr ->
        throwEdh ets UsageError
          $  "invalid range of "
          <> T.pack (edhTypeNameOf badRngSpec)
          <> ": "
          <> rngRepr
 where
  createRangeCol :: DataType -> Int -> Int -> Int -> STM ()
  createRangeCol !dt !start !stop !step =
    resolveNumDataType ets (data'type'identifier dt) $ \ !ndt ->
      flat'new'range'array ndt ets start stop step $ \ !cs -> do
        !clv <- newTMVar $ flatArrayCapacity cs
        !csv <- newTVar cs
        let !col = Column dt clv csv
        edhCreateHostObj colClass (toDyn col) []
          >>= exitEdh ets exit
          .   EdhObject


-- TODO impl. `linspace` following:
--      https://numpy.org/doc/stable/reference/generated/numpy.linspace.html
-- Note it can be more exact by stepping with LosslessDecimal


-- | resemble https://numpy.org/doc/stable/reference/generated/numpy.where.html
whereProc :: ArgsPack -> EdhHostProc
whereProc (ArgsPack [EdhObject !colBoolIdx] !kwargs) !exit !ets
  | odNull kwargs = castObjectStore colBoolIdx >>= \case
    Nothing -> throwEdh
      ets
      UsageError
      "invalid index object, need to be a column with dtype=yesno"
    Just (_, mcol@(Column !dt _ _)) -> if data'type'identifier dt /= "yesno"
      then
        throwEdh ets UsageError
        $  "invalid dtype="
        <> data'type'identifier dt
        <> " for where(), need to be yesno"
      else nonzeroIdxColumn ets mcol $ \ !colResult ->
        edhCreateHostObj (edh'obj'class colBoolIdx) (toDyn colResult) []
          >>= exitEdh ets exit
          .   EdhObject
whereProc (ArgsPack [EdhObject !_colBoolIdx, !_trueData, !_falseData] !kwargs) _exit !ets
  | odNull kwargs
  = throwEdh ets UsageError "not implemented yet."
whereProc !apk _ !ets =
  throwEdh ets UsageError $ "invalid args to where()" <> T.pack (show apk)

