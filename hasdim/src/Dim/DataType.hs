{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Numpy dtype inspired abstraction for vectorizable types of data
--
-- The data type system is extensible through the effect system of Edh
module Dim.DataType where

import           Prelude
-- import           Debug.Trace

import           System.IO.Unsafe               ( unsafePerformIO )
import           GHC.Conc                       ( unsafeIOToSTM )

import           Foreign

import           Control.Monad.Reader

import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.Coerce
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

emptyFlatArray :: FlatArray a
emptyFlatArray = unsafePerformIO $ do
  !np <- newForeignPtr_ nullPtr
  return $ FlatArray 0 np
{-# NOINLINE emptyFlatArray #-}

newFlatArray :: forall a . Storable a => Int -> IO (FlatArray a)
newFlatArray !cap = do
  !p  <- callocArray cap
  !fp <- newForeignPtr finalizerFree p
  return $ FlatArray cap fp

flatArrayCapacity :: FlatArray a -> Int
flatArrayCapacity (FlatArray !cap _) = cap

flatArrayNumBytes :: forall a . Storable a => FlatArray a -> Int
flatArrayNumBytes (FlatArray !cap _) = cap * sizeOf (undefined :: a)

unsafeSliceFlatArray
  :: forall a . (Storable a) => FlatArray a -> Int -> Int -> FlatArray a
unsafeSliceFlatArray (FlatArray _ !fp) !offset !len =
  FlatArray len $ plusForeignPtr fp $ offset * sizeOf (undefined :: a)

unsafeFlatArrayAsVector
  :: (Storable a, EdhXchg a, Storable b, EdhXchg b) => FlatArray a -> Vector b
unsafeFlatArrayAsVector (FlatArray !cap !fp) =
  V.unsafeFromForeignPtr0 (castForeignPtr fp) cap

unsafeFlatArrayFromVector
  :: (Storable a, EdhXchg a, Storable b, EdhXchg b) => Vector a -> FlatArray b
unsafeFlatArrayFromVector !vec = case V.unsafeToForeignPtr0 vec of
  (!fp, !cap) -> FlatArray cap (castForeignPtr fp)

unsafeFlatArrayAsMVector
  :: (Storable a, EdhXchg a, Storable b, EdhXchg b) => FlatArray a -> IOVector b
unsafeFlatArrayAsMVector (FlatArray !cap !fp) =
  MV.unsafeFromForeignPtr0 (castForeignPtr fp) cap

unsafeFlatArrayFromMVector
  :: (Storable a, EdhXchg a, Storable b, EdhXchg b) => IOVector a -> FlatArray b
unsafeFlatArrayFromMVector !mvec = case MV.unsafeToForeignPtr0 mvec of
  (!fp, !cap) -> FlatArray cap (castForeignPtr fp)


type DataTypeIdent = Text

data DataType where
  DataType ::(EdhXchg a, Storable a, Typeable a) => {
      data'type'identifier :: DataTypeIdent
    , data'type'storable :: FlatStorable a
    } -> DataType


createDataTypeClass :: Scope -> STM Object
createDataTypeClass !clsOuterScope =
  mkHostClass' clsOuterScope "dtype" dtypeAllocator [] $ \ !clsScope -> do
    !mths <-
      sequence
      $  [ (AttrByName nm, ) <$> mkHostProc clsScope vc nm hp args
         | (nm, vc, hp, args) <-
           [ ( "=="
             , EdhMethod
             , dtypeEqProc
             , PackReceiver []
             )
-- assuming there's an attribute in context samely named after the
-- identifier for a valid dtype
           , ("__repr__", EdhMethod, dtypeIdentProc, PackReceiver [])
           ]
         ]
      ++ [ (AttrByName nm, ) <$> mkHostProperty clsScope nm getter setter
         | (nm, getter, setter) <- [("id", dtypeIdentProc, Nothing)]
         ]
    iopdUpdate mths $ edh'scope'entity clsScope

 where

  -- | host constructor dtype()
  dtypeAllocator :: EdhObjectAllocator
  -- not really constructable from Edh code, this only creates bogus dtype obj
  dtypeAllocator _ _ !ctorExit = ctorExit =<< HostStore <$> newTVar (toDyn nil)

  dtypeEqProc :: EdhHostProc
  dtypeEqProc (ArgsPack [EdhObject !dtoOther] _) !exit !ets =
    withThisHostObj ets $ \_hsv (DataType !ident _) ->
      withHostObject' dtoOther (exitEdh ets exit $ EdhBool False)
        $ \_hsv (DataType !identOther _) ->
            exitEdh ets exit $ EdhBool $ identOther == ident
  dtypeEqProc _ !exit !ets = exitEdh ets exit $ EdhBool False

  dtypeIdentProc :: EdhHostProc
  dtypeIdentProc _ !exit !ets = withThisHostObj ets
    $ \_hsv (DataType !ident _) -> exitEdh ets exit $ EdhString ident


makeDataType
  :: forall a
   . (EdhXchg a, Storable a, Typeable a)
  => DataTypeIdent
  -> DataType
makeDataType !dti = DataType dti (flatStorable :: FlatStorable a)

-- | FlatStorable facilitates the basic support of a data type to be managable
-- by HasDim, i.e. array allocation, element read/write, array bulk update.
--
-- More sophisticated, vectorized operations are supported by other collections
-- of routines, as they tends to have more demanding premises than required
-- here.
data FlatStorable a where
  FlatStorable ::(EdhXchg a, Storable a, Typeable a) => {
      coerce'flat'array :: FlatArray b -> FlatArray a
    , flat'element'size :: Int
    , flat'element'align :: Int
    , flat'new'array :: Int -> STM (FlatArray a)
    , flat'grow'array :: FlatArray a -> Int -> STM (FlatArray a)
    , flat'array'read :: EdhThreadState -> FlatArray a
        -> Int -> (EdhValue -> STM ()) -> STM ()
    , flat'array'write :: EdhThreadState -> FlatArray a
        -> Int -> EdhValue -> (EdhValue -> STM ()) -> STM ()
    , flat'array'update :: EdhThreadState
        -> [(Int,a)]  -> FlatArray a  -> STM () -> STM ()
  }-> FlatStorable a
 deriving Typeable
flatStorable
  :: forall a . (EdhXchg a, Storable a, Typeable a) => FlatStorable a
flatStorable = FlatStorable coerceArray
                            (sizeOf (undefined :: a))
                            (alignment (undefined :: a))
                            createArray
                            growArray
                            readArrayCell
                            writeArrayCell
                            updateArray
 where
  coerceArray = coerce
  createArray !cap = unsafeIOToSTM (newFlatArray cap)
  growArray (FlatArray !cap !fp) !newCap = unsafeIOToSTM $ do
    !p'  <- callocArray newCap
    !fp' <- newForeignPtr finalizerFree p'
    withForeignPtr fp $ \ !p -> copyArray p' p $ min newCap cap
    return $ FlatArray newCap fp'
  readArrayCell !ets (FlatArray !cap !fp) !idx !exit =
    edhRegulateIndex ets cap idx $ \ !posIdx -> do
      sv <- unsafeIOToSTM $ withForeignPtr fp $ \ !vPtr ->
        peekElemOff vPtr posIdx
      toEdh ets sv $ \ !val -> exit val
  writeArrayCell !ets (FlatArray !cap !fp) !idx !val !exit =
    edhRegulateIndex ets cap idx $ \ !posIdx -> fromEdh ets val $ \ !sv -> do
      unsafeIOToSTM $ withForeignPtr fp $ \ !vPtr -> pokeElemOff vPtr posIdx sv
      toEdh ets sv $ \ !val' -> exit val'
  updateArray _ [] _ !exit = exit
  updateArray !ets ((!idx, !sv) : rest'upds) ary@(FlatArray !cap !fp) !exit =
    edhRegulateIndex ets cap idx $ \ !posIdx -> do
      unsafeIOToSTM $ withForeignPtr fp $ \ !vPtr -> pokeElemOff vPtr posIdx sv
      updateArray ets rest'upds ary exit


-- | A pack of data manipulation routines, per operational category, per data
-- type identifier
data DataManiRoutinePack where
  DataManiRoutinePack ::{
      data'mpk'identifier :: DataTypeIdent
    , data'mpk'category :: Text
    , data'mpk'routines :: Dynamic
    } -> DataManiRoutinePack


createDMRPClass :: Scope -> STM Object
createDMRPClass !clsOuterScope =
  mkHostClass' clsOuterScope "DMRP" dmrpAllocator [] $ \ !clsScope -> do
    !mths <- sequence
      [ (AttrByName nm, ) <$> mkHostProc clsScope vc nm hp mthArgs
      | (nm, vc, hp, mthArgs) <-
        [("__repr__", EdhMethod, dmrpReprProc, PackReceiver [])]
      ]
    iopdUpdate mths $ edh'scope'entity clsScope

 where

  -- | host constructor dmrp()
  dmrpAllocator :: EdhObjectAllocator
  -- not really constructable from Edh code, this only creates bogus dmrp obj
  dmrpAllocator _ _ !ctorExit = ctorExit =<< HostStore <$> newTVar (toDyn nil)

  dmrpReprProc :: EdhHostProc
  dmrpReprProc _ !exit !ets =
    withThisHostObj' ets (exitEdh ets exit $ EdhString "<bogus-dmrp>")
      $ \_hsv (DataManiRoutinePack !ident !cate _) ->
          exitEdh ets exit $ EdhString $ "<dmrp/" <> ident <> "#" <> cate <> ">"


data FlatOrd a where
  FlatOrd ::(Ord a, Storable a, Typeable a, EdhXchg a) => {
      flat'cmp'vectorized :: EdhThreadState -> FlatArray a
        -> (Ordering -> Bool) -> EdhValue -> (FlatArray YesNo -> STM ()) -> STM ()
    , flat'cmp'element'wise :: EdhThreadState -> FlatArray a
        -> (Ordering -> Bool) -> FlatArray a -> (FlatArray YesNo -> STM ()) -> STM ()
  }-> FlatOrd a
 deriving Typeable
flatOrd :: (Ord a, Storable a, Typeable a, EdhXchg a) => FlatOrd a
flatOrd = FlatOrd vecCmp elemCmp
 where
  -- vectorized comparation, yielding a new YesNo array
  vecCmp !ets (FlatArray !cap !fp) !cmp !v !exit = fromEdh ets v $ \ !sv ->
    (exit =<<) $ unsafeIOToSTM $ withForeignPtr fp $ \ !p -> do
      !rp  <- callocArray cap
      !rfp <- newForeignPtr finalizerFree rp
      let go i | i >= cap = return $ FlatArray cap rfp
          go i            = do
            ev <- peekElemOff p i
            pokeElemOff rp i $ if cmp $ compare ev sv then 1 else 0
            go (i + 1)
      go 0
  -- element-wise comparation, yielding a new YesNo array
  elemCmp _ets (FlatArray !cap1 !fp1) !cmp (FlatArray _cap2 !fp2) !exit =
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

resolveDataComparator
  :: forall a
   . (Typeable (FlatOrd a))
  => EdhThreadState
  -> DataTypeIdent
  -> FlatArray a
  -> (FlatOrd a -> STM ())
  -> STM ()
resolveDataComparator !ets !dti !fa =
  resolveDataComparator' ets dti fa
    $  throwEdh ets UsageError
    $  "ordering not supported by dtype: "
    <> dti
resolveDataComparator'
  :: forall a
   . (Typeable (FlatOrd a))
  => EdhThreadState
  -> DataTypeIdent
  -> FlatArray a
  -> STM ()
  -> (FlatOrd a -> STM ())
  -> STM ()
resolveDataComparator' !ets !dti _ !naExit !exit =
  runEdhTx ets
    $ performEdhEffect (AttrBySym resolveDataComparatorEffId) [EdhString dti] []
    $ \case
        EdhNil           -> \_ets -> naExit
        EdhObject !dmrpo -> \_ets ->
          withHostObject' dmrpo naExit
            $ \_hsv (DataManiRoutinePack _dmrp'dti _dmrp'cate !drp) ->
                case fromDynamic drp of
                  Nothing  -> naExit
                  Just !rp -> exit rp
        !badDtVal ->
          throwEdhTx UsageError
            $  "bad return type from @resolveDataComparator(dti): "
            <> T.pack (edhTypeNameOf badDtVal)
resolveDataComparatorEffId :: Symbol
resolveDataComparatorEffId = globalSymbol "@resolveDataComparator"


-- | The ultimate fallback to have trivial data types resolved
resolveDataComparatorProc :: Object -> EdhHostProc
resolveDataComparatorProc !dmrpClass (ArgsPack [EdhString !dti] !kwargs) !exit !ets
  | odNull kwargs
  = case dti of
    "float64" -> exitWith $ toDyn (flatOrd :: FlatOrd Double)
    "float32" -> exitWith $ toDyn (flatOrd :: FlatOrd Float)
    "int64"   -> exitWith $ toDyn (flatOrd :: FlatOrd Int64)
    "int32"   -> exitWith $ toDyn (flatOrd :: FlatOrd Int32)
    "int8"    -> exitWith $ toDyn (flatOrd :: FlatOrd Int8)
    "byte"    -> exitWith $ toDyn (flatOrd :: FlatOrd Int8)
    "intp"    -> exitWith $ toDyn (flatOrd :: FlatOrd Int)
    "yesno"   -> exitWith $ toDyn (flatOrd :: FlatOrd YesNo)
    _ ->
      throwEdh ets UsageError
        $  "a non-trivial data type requested,"
        <> " you may have some framework/lib to provide an effective dtype"
        <> " identified by: "
        <> dti
 where
  exitWith !drp =
    edhCreateHostObj dmrpClass (toDyn $ DataManiRoutinePack dti "cmp" drp) []
      >>= exitEdh ets exit
      .   EdhObject
resolveDataComparatorProc _ _ _ !ets =
  throwEdh ets UsageError "invalid args to @resolveDataComparator(dti)"


data FlatOp a where
  FlatOp ::(EdhXchg a, Storable a, Typeable a) => {
      flat'extract'yesno :: EdhThreadState -> FlatArray YesNo -> FlatArray a
        -> ((FlatArray a, Int) -> STM ()) -> STM ()
    , flat'extract'fancy :: EdhThreadState -> FlatArray Int -> FlatArray a
        -> (FlatArray a -> STM ()) -> STM ()

    , flat'op'vectorized :: EdhThreadState -> FlatArray a
        -> Dynamic -> EdhValue -> (FlatArray a -> STM ()) -> STM ()
    , flat'op'element'wise :: EdhThreadState -> FlatArray a
        -> Dynamic -> FlatArray a -> (FlatArray a -> STM ()) -> STM ()

    , flat'inp'vectorized :: EdhThreadState -> FlatArray a
        -> Dynamic -> EdhValue -> STM () -> STM ()
    , flat'inp'vectorized'slice :: EdhThreadState -> (Int,Int,Int) -> FlatArray a
        -> Dynamic -> EdhValue -> STM () -> STM ()
    , flat'inp'vectorized'masked :: EdhThreadState -> FlatArray YesNo -> FlatArray a
        -> Dynamic -> EdhValue -> STM () -> STM ()
    , flat'inp'vectorized'fancy :: EdhThreadState -> FlatArray Int -> FlatArray a
        -> Dynamic -> EdhValue -> STM () -> STM ()

    , flat'inp'element'wise :: EdhThreadState -> FlatArray a
        -> Dynamic -> FlatArray a -> STM () -> STM ()
    , flat'inp'element'wise'slice :: EdhThreadState -> (Int,Int,Int) -> FlatArray a
        -> Dynamic -> FlatArray a -> STM () -> STM ()
    , flat'inp'element'wise'masked :: EdhThreadState -> FlatArray YesNo -> FlatArray a
        -> Dynamic -> FlatArray a -> STM () -> STM ()
    , flat'inp'element'wise'fancy :: EdhThreadState -> FlatArray Int -> FlatArray a
        -> Dynamic -> FlatArray a -> STM () -> STM ()
  }-> FlatOp a
 deriving Typeable
flatOp :: (EdhXchg a, Storable a, Typeable a) => FlatOp a
flatOp = FlatOp vecExtractBool
                vecExtractFancy
                vecOp
                elemOp
                vecInp
                vecInpSlice
                vecInpMasked
                vecInpFancy
                elemInp
                elemInpSlice
                elemInpMasked
                elemInpFancy
 where
  -- vectorized data extraction with a yesno index, yielding a new array
  vecExtractBool _ets (FlatArray !mcap !mfp) (FlatArray _cap !fp) !exit =
    (exit =<<) $ unsafeIOToSTM $ withForeignPtr mfp $ \ !mp ->
      withForeignPtr fp $ \ !p -> do
        !rp  <- callocArray mcap
        !rfp <- newForeignPtr finalizerFree rp
        let go i ri | i >= mcap = return (FlatArray mcap rfp, ri)
            go i ri             = do
              mv <- peekElemOff mp i
              if mv /= 0
                then do
                  peekElemOff p i >>= pokeElemOff rp ri
                  go (i + 1) (ri + 1)
                else go (i + 1) ri
        go 0 0
  -- vectorized data extraction with a fancy index, yielding a new array
  vecExtractFancy !ets (FlatArray !icap !ifp) (FlatArray !cap !fp) !exit = do
    !result <- unsafeIOToSTM $ withForeignPtr fp $ \ !p ->
      withForeignPtr ifp $ \ !ip -> do
        !rp  <- callocArray icap
        !rfp <- newForeignPtr finalizerFree rp
        let go i | i >= icap = return $ Right $ FlatArray icap rfp
            go i             = do
              idx <- peekElemOff ip i
              if idx < 0 || idx >= cap
                then return $ Left idx
                else do
                  peekElemOff p idx >>= pokeElemOff rp i
                  go (i + 1)
        go 0
    case result of
      Left !badIdx ->
        throwEdh ets EvalError
          $  "fancy index out of bounds: "
          <> T.pack (show badIdx)
          <> " vs "
          <> T.pack (show cap)
      Right !rtnAry -> exit rtnAry
  -- vectorized operation, yielding a new array
  vecOp !ets (FlatArray !cap !fp) !dop !v !exit = case fromDynamic dop of
    Nothing                  -> error "bug: dtype op type mismatch"
    Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv ->
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
  elemOp _ets (FlatArray !cap1 !fp1) !dop (FlatArray _cap2 !fp2) !exit =
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
  vecInp !ets (FlatArray !cap !fp) !dop !v !exit = case fromDynamic dop of
    Nothing                  -> error "bug: dtype op type mismatch"
    Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv ->
      (>> exit) $ unsafeIOToSTM $ withForeignPtr fp $ \ !p -> do
        let go i | i >= cap = return ()
            go i            = do
              ev <- peekElemOff p i
              pokeElemOff p i $ op ev sv
              go (i + 1)
        go 0
  -- vectorized operation, inplace modifying the array, with a slice spec
  vecInpSlice !ets (!start, !stop, !step) (FlatArray _cap !fp) !dop !v !exit =
    case fromDynamic dop of
      Nothing                  -> error "bug: dtype op type mismatch"
      Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv ->
        (>> exit) $ unsafeIOToSTM $ withForeignPtr fp $ \ !p -> do
          let (q, r) = quotRem (stop - start) step
              !len   = if r == 0 then abs q else 1 + abs q
          let go _ i | i >= len = return ()
              go n i            = do
                ev <- peekElemOff p n
                pokeElemOff p n $ op ev sv
                go (n + step) (i + 1)
          go start 0
  -- vectorized operation, inplace modifying the array, with a yesno mask
  vecInpMasked !ets (FlatArray _cap !mfp) (FlatArray !cap !fp) !dop !v !exit =
    case fromDynamic dop of
      Nothing                  -> error "bug: dtype op type mismatch"
      Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv ->
        (>> exit) $ unsafeIOToSTM $ withForeignPtr mfp $ \ !mp ->
          withForeignPtr fp $ \ !p -> do
            let go i | i >= cap = return ()
                go i            = do
                  mv <- peekElemOff mp i
                  when (mv /= 0) $ do
                    ev <- peekElemOff p i
                    pokeElemOff p i $ op ev sv
                  go (i + 1)
            go 0
  -- vectorized operation, inplace modifying the array, with a fancy index
  vecInpFancy !ets (FlatArray !icap !ifp) (FlatArray !cap !fp) !dop !v !exit =
    case fromDynamic dop of
      Nothing                  -> error "bug: dtype op type mismatch"
      Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv -> do
        !badIdx <- unsafeIOToSTM $ withForeignPtr ifp $ \ !ip ->
          withForeignPtr fp $ \ !p -> do
            let go i | i >= icap = return 0
                go i = peekElemOff ip i >>= \ !idx -> if idx < 0 || idx >= cap
                  then return idx
                  else do
                    ev <- peekElemOff p idx
                    pokeElemOff p idx $ op ev sv
                    go (i + 1)
            go 0
        if badIdx == 0
          then exit
          else
            throwEdh ets EvalError
            $  "fancy index out of bounds: "
            <> T.pack (show badIdx)
            <> " vs "
            <> T.pack (show cap)
  -- element-wise operation, inplace modifying array
  elemInp _ets (FlatArray !cap1 !fp1) !dop (FlatArray _cap2 !fp2) !exit =
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
  -- element-wise operation, inplace modifying array, with a slice spec
  elemInpSlice _ets (!start, !stop, !step) (FlatArray _cap1 !fp1) !dop (FlatArray !cap2 !fp2) !exit
    = case fromDynamic dop of
      Nothing -> error "bug: dtype op type mismatch"
      Just (op :: a -> a -> a) ->
        (>> exit) $ unsafeIOToSTM $ withForeignPtr fp1 $ \ !p1 ->
          withForeignPtr fp2 $ \ !p2 -> do
            let (q, r) = quotRem (stop - start) step
                !len   = min cap2 $ if r == 0 then abs q else 1 + abs q
            let go _ i | i >= len = return ()
                go n i            = do
                  ev1 <- peekElemOff p1 n
                  ev2 <- peekElemOff p2 i
                  pokeElemOff p1 n $ op ev1 ev2
                  go (n + step) (i + 1)
            go start 0
  -- element-wise operation, inplace modifying array, with a yesno mask
  elemInpMasked _ets (FlatArray _cap !mfp) (FlatArray !cap1 !fp1) !dop (FlatArray _cap2 !fp2) !exit
    = case fromDynamic dop of
      Nothing -> error "bug: dtype op type mismatch"
      Just (op :: a -> a -> a) ->
        (>> exit)
          $ unsafeIOToSTM
          $ withForeignPtr mfp
          $ \ !mp -> withForeignPtr fp1 $ \ !p1 ->
              withForeignPtr fp2 $ \ !p2 -> do
                let go i | i >= cap1 = return ()
                    go i             = do
                      mv <- peekElemOff mp i
                      when (mv /= 0) $ do
                        ev1 <- peekElemOff p1 i
                        ev2 <- peekElemOff p2 i
                        pokeElemOff p1 i $ op ev1 ev2
                      go (i + 1)
                go 0
  -- element-wise operation, inplace modifying array, with a fancy index
  elemInpFancy !ets (FlatArray !icap !ifp) (FlatArray !cap1 !fp1) !dop (FlatArray !cap2 !fp2) !exit
    = case fromDynamic dop of
      Nothing                  -> error "bug: dtype op type mismatch"
      Just (op :: a -> a -> a) -> do
        !badIdx <-
          unsafeIOToSTM
          $ withForeignPtr ifp
          $ \ !ip -> withForeignPtr fp1 $ \ !p1 ->
              withForeignPtr fp2 $ \ !p2 -> do
                let len = min icap cap2
                let go i | i >= len = return 0
                    go i            = peekElemOff ip i >>= \ !idx ->
                      if idx < 0 || idx >= cap1
                        then return idx
                        else do
                          ev1 <- peekElemOff p1 idx
                          ev2 <- peekElemOff p2 i
                          pokeElemOff p1 idx $ op ev1 ev2
                          go (i + 1)
                go 0
        if badIdx == 0
          then exit
          else
            throwEdh ets EvalError
            $  "fancy index out of bounds: "
            <> T.pack (show badIdx)
            <> " vs "
            <> T.pack (show cap1)

resolveDataOperator
  :: forall a
   . (Typeable (FlatOp a))
  => EdhThreadState
  -> DataTypeIdent
  -> FlatArray a
  -> (FlatOp a -> STM ())
  -> STM ()
resolveDataOperator !ets !dti !fa =
  resolveDataOperator' ets dti fa
    $  throwEdh ets UsageError
    $  "operation not supported by dtype: "
    <> dti
resolveDataOperator'
  :: forall a
   . (Typeable (FlatOp a))
  => EdhThreadState
  -> DataTypeIdent
  -> FlatArray a
  -> STM ()
  -> (FlatOp a -> STM ())
  -> STM ()
resolveDataOperator' !ets !dti _ !naExit !exit =
  runEdhTx ets
    $ performEdhEffect (AttrBySym resolveDataOperatorEffId) [EdhString dti] []
    $ \case
        EdhNil           -> \_ets -> naExit
        EdhObject !dmrpo -> \_ets ->
          withHostObject' dmrpo naExit
            $ \_hsv (DataManiRoutinePack _dmrp'dti _dmrp'cate !drp) ->
                case fromDynamic drp of
                  Nothing ->
                    throwEdh ets UsageError
                      $ "bug: data manipulation routine pack obtained for dtype "
                      <> dti
                      <> " mismatch the flat array type created from it."
                  Just !rp -> exit rp
        !badDtVal ->
          throwEdhTx UsageError
            $  "bad return type from @resolveDataOperator(dti): "
            <> T.pack (edhTypeNameOf badDtVal)
resolveDataOperatorEffId :: Symbol
resolveDataOperatorEffId = globalSymbol "@resolveDataOperator"


-- | The ultimate fallback to have trivial data types resolved
resolveDataOperatorProc :: Object -> EdhHostProc
resolveDataOperatorProc !dmrpClass (ArgsPack [EdhString !dti] !kwargs) !exit !ets
  | odNull kwargs
  = case dti of
    "float64" -> exitWith $ toDyn (flatOp :: FlatOp Double)
    "float32" -> exitWith $ toDyn (flatOp :: FlatOp Float)
    "int64"   -> exitWith $ toDyn (flatOp :: FlatOp Int64)
    "int32"   -> exitWith $ toDyn (flatOp :: FlatOp Int32)
    "int8"    -> exitWith $ toDyn (flatOp :: FlatOp Int8)
    "byte"    -> exitWith $ toDyn (flatOp :: FlatOp Int8)
    "intp"    -> exitWith $ toDyn (flatOp :: FlatOp Int)
    "yesno"   -> exitWith $ toDyn (flatOp :: FlatOp YesNo)
    _ ->
      throwEdh ets UsageError
        $  "a non-trivial data type requested,"
        <> " you may have some framework/lib to provide an effective dtype"
        <> " identified by: "
        <> dti
 where
  exitWith !drp =
    edhCreateHostObj dmrpClass (toDyn $ DataManiRoutinePack dti "op" drp) []
      >>= exitEdh ets exit
      .   EdhObject
resolveDataOperatorProc _ _ _ !ets =
  throwEdh ets UsageError "invalid args to @resolveDataOperator(dti)"


createNumDataTypeClass :: Scope -> STM Object
createNumDataTypeClass !clsOuterScope =
  mkHostClass' clsOuterScope "NumDataType" numdtAllocator [] $ \ !clsScope -> do
    !mths <-
      sequence
      $  [ (AttrByName nm, ) <$> mkHostProc clsScope vc nm hp args
         | (nm, vc, hp, args) <-
           [ ("=="      , EdhMethod, numdtEqProc   , PackReceiver [])
           , ("__repr__", EdhMethod, numdtIdentProc, PackReceiver [])
           ]
         ]
      ++ [ (AttrByName nm, ) <$> mkHostProperty clsScope nm getter setter
         | (nm, getter, setter) <- [("id", numdtIdentProc, Nothing)]
         ]
    iopdUpdate mths $ edh'scope'entity clsScope

 where

  -- | host constructor numdt()
  numdtAllocator :: EdhObjectAllocator
  -- not really constructable from Edh code, this only creates bogus numdt obj
  numdtAllocator _ _ !ctorExit = ctorExit =<< HostStore <$> newTVar (toDyn nil)

  numdtEqProc :: EdhHostProc
  numdtEqProc (ArgsPack [EdhObject !dtoOther] _) !exit !ets =
    withThisHostObj ets $ \_hsv (NumDataType !ident _) ->
      withHostObject' dtoOther (exitEdh ets exit $ EdhBool False)
        $ \_hsv (NumDataType !identOther _) ->
            exitEdh ets exit $ EdhBool $ identOther == ident
  numdtEqProc _ !exit !ets = exitEdh ets exit $ EdhBool False

  numdtIdentProc :: EdhHostProc
  numdtIdentProc _ !exit !ets =
    withThisHostObj' ets (exitEdh ets exit $ EdhString "<bogus-numdt>")
      $ \_hsv (NumDataType !ident _) ->
          exitEdh ets exit $ EdhString $ "<numeric-dtype:" <> ident <> ">"


resolveNumDataType
  :: EdhThreadState -> DataTypeIdent -> (NumDataType -> STM ()) -> STM ()
resolveNumDataType !ets !dti =
  resolveNumDataType' ets dti
    $  throwEdh ets UsageError
    $  "not an applicable numeric dtype: "
    <> dti
resolveNumDataType'
  :: EdhThreadState
  -> DataTypeIdent
  -> STM ()
  -> (NumDataType -> STM ())
  -> STM ()
resolveNumDataType' !ets !dti !naExit !exit =
  runEdhTx ets
    $ performEdhEffect (AttrBySym resolveNumDataTypeEffId) [EdhString dti] []
    $ \case
        EdhNil -> \_ets -> naExit
        EdhObject !ndto ->
          \_ets -> withHostObject' ndto naExit $ \_hsv !ndt -> exit ndt
        !badDtVal ->
          throwEdhTx UsageError
            $  "bad return type from @resolveNumDataType(dti): "
            <> T.pack (edhTypeNameOf badDtVal)
resolveNumDataTypeEffId :: Symbol
resolveNumDataTypeEffId = globalSymbol "@resolveNumDataType"


-- | The ultimate fallback to have trivial data types resolved
resolveNumDataTypeProc :: Object -> EdhHostProc
resolveNumDataTypeProc !numdtClass (ArgsPack [EdhString !dti] !kwargs) !exit !ets
  | odNull kwargs
  = case dti of
    "float64" ->
      exitWith $ toDyn $ NumDataType dti (flatRanger :: FlatRanger Double)
    "float32" ->
      exitWith $ toDyn $ NumDataType dti (flatRanger :: FlatRanger Float)
    "int64" ->
      exitWith $ toDyn $ NumDataType dti (flatRanger :: FlatRanger Int64)
    "int32" ->
      exitWith $ toDyn $ NumDataType dti (flatRanger :: FlatRanger Int32)
    "int8" ->
      exitWith $ toDyn $ NumDataType dti (flatRanger :: FlatRanger Int8)
    "byte" ->
      exitWith $ toDyn $ NumDataType dti (flatRanger :: FlatRanger Int8)
    "intp" -> exitWith $ toDyn $ NumDataType dti (flatRanger :: FlatRanger Int)
    _ ->
      throwEdh ets UsageError
        $  "a non-trivial numeric data type requested,"
        <> " you may have some framework/lib to provide an effective numdt"
        <> " identified by: "
        <> dti
 where
  exitWith !dndt =
    edhCreateHostObj numdtClass dndt [] >>= exitEdh ets exit . EdhObject
resolveNumDataTypeProc _ _ _ !ets =
  throwEdh ets UsageError "invalid args to @resolveNumDataType(dti)"


data NumDataType where
  NumDataType ::(Num a, EdhXchg a, Storable a, Typeable a) => {
      num'type'identifier :: !DataTypeIdent
    , num'type'ranger :: !(FlatRanger a)
    } -> NumDataType


data FlatRanger a where
  FlatRanger ::(Num a, EdhXchg a, Storable a, Typeable a) => {
      flat'new'range'array :: EdhThreadState
        -> Int -> Int -> Int -> (FlatArray a -> STM ()) -> STM ()
    , flat'new'nonzero'array :: EdhThreadState
        -> FlatArray YesNo -> ((FlatArray a, Int) -> STM ()) -> STM ()
    }-> FlatRanger a
 deriving Typeable
flatRanger
  :: forall a . (Num a, EdhXchg a, Storable a, Typeable a) => FlatRanger a
flatRanger = FlatRanger rangeCreator nonzeroCreator
 where
  rangeCreator _ !start !stop _ !exit | stop == start = exit (emptyFlatArray @a)
  rangeCreator !ets !start !stop !step !exit =
    if (stop > start && step <= 0) || (stop < start && step >= 0)
      then throwEdh ets UsageError "range is not converging"
      else (exit =<<) $ unsafeIOToSTM $ do
        let (q, r) = quotRem (stop - start) step
            !len   = if r == 0 then abs q else 1 + abs q
        !p  <- callocArray @a len
        !fp <- newForeignPtr finalizerFree p
        let fillRng :: Int -> Int -> IO ()
            fillRng !n !i = if i >= len
              then return ()
              else do
                pokeElemOff p i $ fromIntegral n
                fillRng (n + step) (i + 1)
        fillRng start 0
        return $ FlatArray len fp
  nonzeroCreator _ (FlatArray !mcap !mfp) !exit =
    (exit =<<) $ unsafeIOToSTM $ withForeignPtr mfp $ \ !mp -> do
      !rp  <- callocArray @a mcap
      !rfp <- newForeignPtr finalizerFree rp
      let go i ri | i >= mcap = return (FlatArray mcap rfp, ri)
          go i ri             = do
            mv <- peekElemOff mp i
            if mv /= 0
              then do
                pokeElemOff rp ri $ fromIntegral i
                go (i + 1) (ri + 1)
              else go (i + 1) ri
      go 0 0
