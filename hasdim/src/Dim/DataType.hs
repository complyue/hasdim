
-- | Numpy dtype inspired abstraction for vectorizable types of data
module Dim.DataType where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Foreign

import           Control.Monad.Reader

import           Control.Concurrent.STM


import           Data.Text                      ( Text )
import           Data.Dynamic

import           Data.Vector.Storable           ( Vector )
import qualified Data.Vector.Storable          as V
import           Data.Vector.Storable.Mutable   ( IOVector )
import qualified Data.Vector.Storable.Mutable  as MV

import           Language.Edh.EHI

import           Dim.XCHG


data FlatArray a = FlatArray
    {-# UNPACK #-} !Int            -- ^ capacity
    {-# UNPACK #-} !(ForeignPtr a) -- ^ mem ref
  deriving ( Typeable )

flatArrayCapacity :: FlatArray a -> Int
flatArrayCapacity (FlatArray !cap _) = cap

flatArrayNumBytes :: forall a . Storable a => FlatArray a -> Int
flatArrayNumBytes (FlatArray !cap _) = cap * sizeOf (undefined :: a)

unsafeSliceFlatArray :: forall a . FlatArray a -> Int -> Int -> FlatArray a
unsafeSliceFlatArray (FlatArray _ !fp) !offset !len =
  FlatArray len $ plusForeignPtr fp offset

unsafeFlatArrayToVector
  :: (Storable a, EdhXchg a, Storable b, EdhXchg b) => FlatArray a -> Vector b
unsafeFlatArrayToVector (FlatArray !cap !fp) =
  V.unsafeFromForeignPtr0 (castForeignPtr fp) cap

unsafeFlatArrayFromVector
  :: (Storable a, EdhXchg a, Storable b, EdhXchg b) => Vector a -> FlatArray b
unsafeFlatArrayFromVector !vec = case V.unsafeToForeignPtr0 vec of
  (!fp, !cap) -> FlatArray cap (castForeignPtr fp)

unsafeFlatArrayToMVector
  :: (Storable a, EdhXchg a, Storable b, EdhXchg b) => FlatArray a -> IOVector b
unsafeFlatArrayToMVector (FlatArray !cap !fp) =
  MV.unsafeFromForeignPtr0 (castForeignPtr fp) cap

unsafeFlatArrayFromMVector
  :: (Storable a, EdhXchg a, Storable b, EdhXchg b) => IOVector a -> FlatArray b
unsafeFlatArrayFromMVector !mvec = case MV.unsafeToForeignPtr0 mvec of
  (!fp, !cap) -> FlatArray cap (castForeignPtr fp)


-- type safe data manipulation operations wrt to exchanging data with Edh
-- programs
data DataType a where
  DataType ::(Num a, Ord a, Storable a, Typeable a, EdhXchg a) => {
      data'type'identifier :: Text
    , data'element'size :: Int
    , data'element'align :: Int
    , create'flat'array :: EdhProgState
        -> Int -> (FlatArray a -> STM ()) -> STM ()
    , grow'flat'array :: EdhProgState
        -> FlatArray a -> Int -> (FlatArray a -> STM ()) -> STM ()
    , create'range'array :: EdhProgState
        -> Int -> Int -> Int -> (FlatArray a -> STM ()) -> STM ()
    , read'flat'array'cell :: EdhProgState
        -> Int -> FlatArray a -> (EdhValue -> STM ()) -> STM ()
    , write'flat'array'cell :: EdhProgState
        -> EdhValue -> Int -> FlatArray a -> (EdhValue -> STM ()) -> STM ()
    , update'flat'array :: EdhProgState
        -> [(Int,a)]  -> FlatArray a  -> STM () -> STM ()
    , dt'cmp'vectorized :: EdhProgState -> FlatArray a
        -> (Ordering -> Bool) -> EdhValue -> (FlatArray Int8 -> STM ()) -> STM ()
    , dt'cmp'element'wise :: EdhProgState -> FlatArray a
        -> (Ordering -> Bool) -> FlatArray a -> (FlatArray Int8 -> STM ()) -> STM ()
    , dt'op'vectorized :: EdhProgState -> FlatArray a
        -> Dynamic -> EdhValue -> (FlatArray a -> STM ()) -> STM ()
    , dt'op'element'wise :: EdhProgState -> FlatArray a
        -> Dynamic -> FlatArray a -> (FlatArray a -> STM ()) -> STM ()
    , dt'inp'vectorized :: EdhProgState -> FlatArray a
        -> Dynamic -> EdhValue -> STM () -> STM ()
    , dt'inp'element'wise :: EdhProgState -> FlatArray a
        -> Dynamic -> FlatArray a -> STM () -> STM ()
  }-> DataType a
 deriving Typeable
dataType
  :: forall a
   . (Num a, Ord a, Storable a, Typeable a, EdhXchg a)
  => Text
  -> DataType a
dataType !ident = DataType ident
                           (sizeOf (undefined :: a))
                           (alignment (undefined :: a))
                           createArray
                           growArray
                           createRange
                           readArrayCell
                           writeArrayCell
                           updateArray
                           vecCmp
                           elemCmp
                           vecOp
                           elemOp
                           vecInp
                           elemInp
 where
  createArray !_ !cap !exit = (exit =<<) $ unsafeIOToSTM $ do
    !p  <- callocArray cap
    !fp <- newForeignPtr finalizerFree p
    return $ FlatArray cap fp
  growArray _ (FlatArray !cap !fp) !newCap !exit = if newCap <= cap
    then exit $ FlatArray newCap fp
    else (exit =<<) $ unsafeIOToSTM $ do
      !p'  <- callocArray newCap
      !fp' <- newForeignPtr finalizerFree p'
      withForeignPtr fp $ \ !p -> copyArray p' p cap
      return $ FlatArray newCap fp'
  createRange !pgs !start !stop _step !exit | stop == start =
    createArray pgs 0 exit
  createRange !pgs !start !stop !step !exit =
    if (stop > start && step <= 0) || (stop < start && step >= 0)
      then throwEdhSTM pgs UsageError "Range is not converging"
      else (exit =<<) $ unsafeIOToSTM $ do
        let (q, r) = quotRem (stop - start) step
            !len   = if r == 0 then abs q else 1 + abs q
            fillRng :: Ptr a -> Int -> Int -> IO ()
            fillRng !p !n !i = if i >= len
              then return ()
              else do
                pokeElemOff p i $ fromIntegral n
                fillRng p (n + step) (i + 1)
        !p  <- callocArray len
        !fp <- newForeignPtr finalizerFree p
        fillRng p start 0
        return $ FlatArray len fp
  readArrayCell !pgs !idx (FlatArray !cap !fp) !exit =
    edhRegulateIndex pgs cap idx $ \ !posIdx -> do
      sv <- unsafeIOToSTM $ withForeignPtr fp $ \ !vPtr ->
        peekElemOff vPtr posIdx
      toEdh pgs sv $ \ !val -> exit val
  writeArrayCell !pgs !val !idx (FlatArray !cap !fp) !exit =
    edhRegulateIndex pgs cap idx $ \ !posIdx -> fromEdh pgs val $ \ !sv -> do
      unsafeIOToSTM $ withForeignPtr fp $ \ !vPtr -> pokeElemOff vPtr posIdx sv
      toEdh pgs sv $ \ !val' -> exit val'
  updateArray _ [] _ !exit = exit
  updateArray !pgs ((!idx, !sv) : rest'upds) ary@(FlatArray !cap !fp) !exit =
    edhRegulateIndex pgs cap idx $ \ !posIdx -> do
      unsafeIOToSTM $ withForeignPtr fp $ \ !vPtr -> pokeElemOff vPtr posIdx sv
      updateArray pgs rest'upds ary exit
  -- vectorized comparation, yielding a new Int8 array
  vecCmp !pgs (FlatArray !cap !fp) !cmp !v !exit = fromEdh pgs v $ \ !sv ->
    (exit =<<) $ unsafeIOToSTM $ withForeignPtr fp $ \ !p -> do
      !rp  <- callocArray cap
      !rfp <- newForeignPtr finalizerFree rp
      let go i | i >= cap = return $ FlatArray cap rfp
          go i            = do
            ev <- peekElemOff p i
            pokeElemOff rp i $ if cmp $ compare ev sv then 1 else 0
            go (i + 1)
      go 0
  -- element-wise comparation, yielding a new Int8 array
  elemCmp _pgs (FlatArray !cap1 !fp1) !cmp (FlatArray _cap2 !fp2) !exit =
    (exit =<<) $ unsafeIOToSTM $ withForeignPtr fp1 $ \ !p1 ->
      withForeignPtr fp2 $ \ !p2 -> do
        !rp  <- callocArray cap1
        !rfp <- newForeignPtr finalizerFree rp
        let go i | i >= cap1 = return $ FlatArray cap1 rfp
            go i             = do
              ev1 <- peekElemOff p1 i
              ev2 <- peekElemOff p2 i
              pokeElemOff rp i $ if cmp $ compare ev1 ev2 then 1 else 0
              go (i + 1)
        go 0
  -- vectorized operation, yielding a new array
  vecOp !pgs (FlatArray !cap !fp) !dop !v !exit = case fromDynamic dop of
    Nothing                  -> error "bug: dtype op type mismatch"
    Just (op :: a -> a -> a) -> fromEdh pgs v $ \ !sv ->
      (exit =<<) $ unsafeIOToSTM $ withForeignPtr fp $ \ !p -> do
        !rp  <- callocArray cap
        !rfp <- newForeignPtr finalizerFree rp
        let go i | i >= cap = return $ FlatArray cap rfp
            go i            = do
              ev <- peekElemOff p i
              pokeElemOff rp i $ op ev sv
              go (i + 1)
        go 0
  -- element-wise operation, yielding a new array
  elemOp _pgs (FlatArray !cap1 !fp1) !dop (FlatArray _cap2 !fp2) !exit =
    case fromDynamic dop of
      Nothing -> error "bug: dtype op type mismatch"
      Just (op :: a -> a -> a) ->
        (exit =<<) $ unsafeIOToSTM $ withForeignPtr fp1 $ \ !p1 ->
          withForeignPtr fp2 $ \ !p2 -> do
            !rp  <- callocArray cap1
            !rfp <- newForeignPtr finalizerFree rp
            let go i | i >= cap1 = return $ FlatArray cap1 rfp
                go i             = do
                  ev1 <- peekElemOff p1 i
                  ev2 <- peekElemOff p2 i
                  pokeElemOff rp i $ op ev1 ev2
                  go (i + 1)
            go 0
  -- vectorized operation, inplace modifying the array
  vecInp !pgs (FlatArray !cap !fp) !dop !v !exit = case fromDynamic dop of
    Nothing                  -> error "bug: dtype op type mismatch"
    Just (op :: a -> a -> a) -> fromEdh pgs v $ \ !sv ->
      (>> exit) $ unsafeIOToSTM $ withForeignPtr fp $ \ !p -> do
        let go i | i >= cap = return ()
            go i            = do
              ev <- peekElemOff p i
              pokeElemOff p i $ op ev sv
              go (i + 1)
        go 0
  -- element-wise operation, inplace modifying array
  elemInp _pgs (FlatArray !cap1 !fp1) !dop (FlatArray _cap2 !fp2) !exit =
    case fromDynamic dop of
      Nothing -> error "bug: dtype op type mismatch"
      Just (op :: a -> a -> a) ->
        (>> exit) $ unsafeIOToSTM $ withForeignPtr fp1 $ \ !p1 ->
          withForeignPtr fp2 $ \ !p2 -> do
            let go i | i >= cap1 = return ()
                go i             = do
                  ev1 <- peekElemOff p1 i
                  ev2 <- peekElemOff p2 i
                  pokeElemOff p1 i $ op ev1 ev2
                  go (i + 1)
            go 0


data ConcreteDataType where
  ConcreteDataType ::(Ord a, Storable a, EdhXchg a) => {
      concrete'data'type :: !(DataType a)
    } -> ConcreteDataType
 deriving Typeable
instance Eq ConcreteDataType where
  ConcreteDataType x == ConcreteDataType y =
    data'type'identifier x == data'type'identifier y


-- | host Class dtype()
dtypeCtor :: EdhHostCtor
-- not really constructable from Edh code, relies on host code to fill
-- the in-band storage
dtypeCtor _ _ !ctorExit = ctorExit $ toDyn nil

dtypeMethods :: EdhProgState -> STM [(AttrKey, EdhValue)]
dtypeMethods !pgsModule =
  sequence
    $  [ (AttrByName nm, ) <$> mkHostProc scope vc nm hp args
       | (nm, vc, hp, args) <-
         [ ( "__init__"
           , EdhMethod
           , dtypeInitProc
           , PackReceiver [mandatoryArg "name"]
           )
         , ("=="      , EdhMethod, dtypeEqProc   , PackReceiver [])
         , ("__repr__", EdhMethod, dtypeIdentProc, PackReceiver [])
         ]
       ]
    ++ [ (AttrByName nm, ) <$> mkHostProperty scope nm getter setter
       | (nm, getter, setter) <- [("id", dtypeIdentProc, Nothing)]
       ]

 where
  !scope = contextScope $ edh'context pgsModule

  dtypeInitProc :: EdhProcedure
  dtypeInitProc (ArgsPack !args _) !exit = case args of
    [EdhString !name] -> ask >>= \ !pgs -> do
      let !dtCls = objClass $ thisObject $ contextScope $ edh'context pgs
      case procedure'lexi dtCls of
        Nothing -> exitEdhProc exit nil
        Just !clsLexi ->
          contEdhSTM $ lookupEdhCtxAttr pgs clsLexi (AttrByName name) >>= \case
            EdhNil -> throwEdhSTM pgs EvalError $ "No such dtype: " <> name
            dtv@(EdhObject !dto) ->
              fromDynamic <$> readTVar (entity'store $ objEntity dto) >>= \case
                Nothing                 -> exitEdhSTM pgs exit nil
                Just ConcreteDataType{} -> exitEdhSTM pgs exit dtv
            _ -> exitEdhSTM pgs exit nil
    _ -> throwEdh UsageError "Invalid args to dtype()"

  dtypeEqProc :: EdhProcedure
  dtypeEqProc (ArgsPack [EdhObject !dtoOther] _) !exit =
    withThatEntity $ \ !pgs cdt@(ConcreteDataType _) ->
      fromDynamic <$> readTVar (entity'store $ objEntity dtoOther) >>= \case
        Nothing -> exitEdhSTM pgs exit $ EdhBool False
        Just cdtOther@(ConcreteDataType _) ->
          exitEdhSTM pgs exit $ EdhBool $ cdtOther == cdt
  dtypeEqProc _ !exit = exitEdhProc exit $ EdhBool False

  dtypeIdentProc :: EdhProcedure
  dtypeIdentProc _ !exit =
    withThatEntity' (\ !pgs -> exitEdhSTM pgs exit $ EdhString "<bad-dtype>")
      $ \ !pgs (ConcreteDataType !dt) ->
          exitEdhSTM pgs exit $ EdhString $ data'type'identifier dt

wrapDataType
  :: EdhProgState
  -> Class
  -> (ConcreteDataType, [Text])
  -> (([Text], EdhValue) -> STM ())
  -> STM ()
wrapDataType !pgs !dtypeClass (cdt@(ConcreteDataType !dt), !alias) !exit' =
  runEdhProc pgs
    $ createEdhObject dtypeClass (ArgsPack [] mempty)
    $ \(OriginalValue !dtypeVal _ _) -> case dtypeVal of
        EdhObject !dtObj -> contEdhSTM $ do
          -- actually fill in the in-band entity storage here
          writeTVar (entity'store $ objEntity dtObj) $ toDyn cdt
          exit' (data'type'identifier dt : alias, dtypeVal)
        _ -> error "bug: createEdhObject returned non-object"

