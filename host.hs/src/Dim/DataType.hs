{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Numpy dtype inspired abstraction for vectorizable types of data
--
-- The data type system is extensible through the effect system of Edh
module Dim.DataType where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Monad
import Data.Dynamic
import Data.Text (Text)
import qualified Data.Text as T
import Data.Typeable (cast)
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Storable.Mutable as MVS
import Dim.XCHG
import Foreign as F
import Foreign.ForeignPtr.Unsafe (unsafeForeignPtrToPtr)
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.EHI
import System.IO.Unsafe (unsafePerformIO)
import System.Random
import Type.Reflection
import Prelude

data FlatArray where
  DeviceArray ::
    (EdhXchg a, Typeable a, Storable a) =>
    { device'array'cap :: !Int,
      device'array'ref :: !(ForeignPtr a)
    } ->
    FlatArray
  HostArray ::
    (EdhXchg a, Typeable a) =>
    { host'array'cap :: !Int,
      host'array'ref :: !(MV.IOVector a)
    } ->
    FlatArray

emptyDeviceArray :: forall a. (EdhXchg a, Typeable a, Storable a) => FlatArray
emptyDeviceArray = unsafePerformIO $ do
  !np <- newForeignPtr_ nullPtr
  return $ DeviceArray @a 0 np
{-# NOINLINE emptyDeviceArray #-}

emptyHostArray :: forall a. (EdhXchg a, Typeable a) => FlatArray
emptyHostArray = unsafePerformIO $ do
  !ha <- MV.new 0
  return $ HostArray @a 0 ha
{-# NOINLINE emptyHostArray #-}

newDeviceArray ::
  forall a.
  (EdhXchg a, Typeable a, Storable a) =>
  Int ->
  IO (ForeignPtr a, FlatArray)
newDeviceArray !cap = do
  !p <- callocArray @a cap
  !fp <- newForeignPtr finalizerFree p
  return (fp, DeviceArray @a cap fp)

newHostArray ::
  forall a.
  (EdhXchg a, Typeable a) =>
  a ->
  Int ->
  IO (MV.IOVector a, FlatArray)
newHostArray !fill'val !cap = do
  !ha <- MV.unsafeNew cap
  MV.set ha fill'val
  return (ha, HostArray @a cap ha)

dupFlatArray :: FlatArray -> Int -> Int -> IO FlatArray
dupFlatArray (DeviceArray !capSrc !fpSrc) !lenSrc !capNew = do
  !p' <- callocArray capNew
  !fp' <- newForeignPtr finalizerFree p'
  withForeignPtr fpSrc $ \ !p -> copyArray p' p $ min capNew (min lenSrc capSrc)
  return $ DeviceArray capNew fp'
dupFlatArray (HostArray _capSrc !haSrc) !lenSrc !capNew = do
  !ha' <- MV.new capNew
  let !cpLen = min lenSrc capNew
  when (cpLen > 0) $
    let !tgt = MV.unsafeSlice 0 cpLen ha'
        !src = MV.unsafeSlice 0 cpLen haSrc
     in MV.copy tgt src
  return $ HostArray capNew ha'

flatArrayCapacity :: FlatArray -> Int
flatArrayCapacity (DeviceArray !cap _) = cap
flatArrayCapacity (HostArray !cap _) = cap

flatArrayNumBytes :: FlatArray -> Int
flatArrayNumBytes (DeviceArray !cap (_fp :: ForeignPtr a)) =
  cap * sizeOf (undefined :: a)
flatArrayNumBytes (HostArray !cap _) = cap * 8

unsafeSliceFlatArray :: FlatArray -> Int -> Int -> FlatArray
unsafeSliceFlatArray (DeviceArray _ (fp :: ForeignPtr a)) !offset !len =
  DeviceArray @a len $
    plusForeignPtr fp $ sizeOf (undefined :: a) * offset
unsafeSliceFlatArray (HostArray _ !ha) !offset !len =
  let !ha' = MV.slice offset len ha in HostArray len ha'

unsafeFlatArrayAsVector :: forall a. (Storable a) => FlatArray -> VS.Vector a
unsafeFlatArrayAsVector (DeviceArray !cap !fp) =
  VS.unsafeFromForeignPtr0 (castForeignPtr fp) cap
unsafeFlatArrayAsVector HostArray {} =
  error "bug: casting host array to storable vector"

unsafeFlatArrayFromVector ::
  forall a. (EdhXchg a, Typeable a, Storable a) => VS.Vector a -> FlatArray
unsafeFlatArrayFromVector !vec = case VS.unsafeToForeignPtr0 vec of
  (!fp, !cap) -> DeviceArray @a cap (castForeignPtr fp)

unsafeFlatArrayAsMVector ::
  forall a.
  (Storable a, EdhXchg a, Typeable a) =>
  FlatArray ->
  MVS.IOVector a
unsafeFlatArrayAsMVector (DeviceArray !cap !fp) =
  MVS.unsafeFromForeignPtr0 (castForeignPtr fp) cap
unsafeFlatArrayAsMVector HostArray {} =
  error "bug: casting host array to storable vector"

unsafeFlatArrayFromMVector ::
  forall a.
  (Storable a, EdhXchg a, Typeable a) =>
  MVS.IOVector a ->
  FlatArray
unsafeFlatArrayFromMVector !mvec = case MVS.unsafeToForeignPtr0 mvec of
  (!fp, !cap) -> DeviceArray @a cap (castForeignPtr fp)

type DataTypeIdent = Text

data DataTypeProxy where
  DeviceDataType ::
    (EdhXchg a, Typeable a, Storable a) =>
    { device'data'type :: !(TypeRep a),
      device'data'size :: !Int,
      device'data'align :: !Int
    } ->
    DataTypeProxy
  HostDataType ::
    (EdhXchg a, Typeable a) =>
    {host'data'default :: !a} ->
    DataTypeProxy

isDataTypeFor :: forall b. Typeable b => DataType -> Bool
isDataTypeFor !dt = case data'type'proxy dt of
  DeviceDataType t _ _ -> case typeRep @b `eqTypeRep` t of
    Just HRefl -> True
    _ -> False
  HostDataType d -> case typeRep @b `eqTypeRep` typeOf d of
    Just HRefl -> True
    _ -> False

-- | DataType facilitates the basic support of a data type to be managable
-- by HasDim, i.e. array allocation, element read/write, array bulk update.
--
-- More sophisticated, vectorized operations are supported by other collections
-- of routines, as they tends to have more demanding premises than required
-- here.
data DataType where
  DataType ::
    { data'type'identifier :: !DataTypeIdent,
      data'type'proxy :: !DataTypeProxy,
      flat'new'array :: Int -> STM FlatArray,
      flat'grow'array :: FlatArray -> Int -> STM FlatArray,
      flat'array'read ::
        EdhThreadState ->
        FlatArray ->
        Int ->
        (EdhValue -> STM ()) ->
        STM (),
      flat'array'write ::
        EdhThreadState ->
        FlatArray ->
        Int ->
        EdhValue ->
        (EdhValue -> STM ()) ->
        STM (),
      flat'array'update ::
        EdhThreadState ->
        [(Int, EdhValue)] ->
        FlatArray ->
        STM () ->
        STM ()
    } ->
    DataType

instance Eq DataType where
  x == y = data'type'identifier x == data'type'identifier y

createDataTypeClass :: Scope -> STM Object
createDataTypeClass !clsOuterScope =
  mkHostClass clsOuterScope "dtype" (allocEdhObj dtypeAllocator) [] $
    \ !clsScope -> do
      !mths <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc clsScope vc nm hp
            | (nm, vc, hp) <-
                [ ("__eq__", EdhMethod, wrapHostProc dtypeEqProc),
                  -- assuming there's an attribute in context samely named
                  -- after the identifier for a valid dtype
                  ("__repr__", EdhMethod, wrapHostProc dtypeIdentProc)
                ]
          ]
            ++ [ (AttrByName nm,) <$> mkHostProperty clsScope nm getter setter
                 | (nm, getter, setter) <- [("id", dtypeIdentProc, Nothing)]
               ]
      iopdUpdate mths $ edh'scope'entity clsScope
  where
    dtypeAllocator :: EdhObjectAllocator
    -- not really constructable from Edh code, this only creates bogus dtype obj
    dtypeAllocator !ctorExit _ = ctorExit Nothing $ HostStore (toDyn nil)

    dtypeEqProc :: EdhValue -> EdhHostProc
    dtypeEqProc !other !exit !ets =
      castObjectStore' other >>= \case
        Nothing -> exitEdh ets exit $ EdhBool False
        Just (_, !dtOther) -> withThisHostObj ets $ \ !dt ->
          exitEdh ets exit $
            EdhBool $
              data'type'identifier dtOther
                == data'type'identifier dt

    dtypeIdentProc :: EdhHostProc
    dtypeIdentProc !exit !ets = withThisHostObj ets $
      \ !dt -> exitEdh ets exit $ EdhString $ data'type'identifier dt

makeDeviceDataType ::
  forall a.
  (EdhXchg a, Typeable a, Storable a) =>
  DataTypeIdent ->
  DataType
makeDeviceDataType !dti =
  DataType
    dti
    ( DeviceDataType
        (typeRep @a)
        (sizeOf (undefined :: a))
        (alignment (undefined :: a))
    )
    createArray
    growArray
    readArrayCell
    writeArrayCell
    updateArray
  where
    createArray !cap = unsafeIOToSTM $ snd <$> newDeviceArray @a cap
    growArray (DeviceArray !cap !fp) !newCap = unsafeIOToSTM $ do
      !p' <- callocArray newCap
      !fp' <- newForeignPtr finalizerFree p'
      withForeignPtr fp $ \ !p -> copyArray p' p $ min newCap cap
      return $ DeviceArray newCap fp'
    growArray _ _ = error "bug: not a device array"
    readArrayCell !ets (DeviceArray !cap !fp) !idx !exit =
      edhRegulateIndex ets cap idx $ \ !posIdx -> do
        !sv <- unsafeIOToSTM $
          withForeignPtr fp $ \ !vPtr ->
            peekElemOff vPtr posIdx
        toEdh ets sv $ \ !val -> exit val
    readArrayCell _ _ _ _ = error "bug: not a device array"
    writeArrayCell !ets (DeviceArray !cap !fp) !idx !val !exit =
      edhRegulateIndex ets cap idx $
        \ !posIdx -> fromEdh ets val $ \ !sv -> do
          unsafeIOToSTM $
            withForeignPtr fp $ \ !vPtr -> pokeElemOff vPtr posIdx sv
          toEdh ets sv $ \ !val' -> exit val'
    writeArrayCell _ _ _ _ _ = error "bug: not a device array"
    updateArray _ [] _ !exit = exit
    updateArray
      !ets
      ((!idx, !val) : rest'upds)
      ary@(DeviceArray !cap !fp)
      !exit =
        edhRegulateIndex ets cap idx $
          \ !posIdx -> fromEdh ets val $ \ !sv -> do
            unsafeIOToSTM $
              withForeignPtr fp $ \ !vPtr -> pokeElemOff vPtr posIdx sv
            updateArray ets rest'upds ary exit
    updateArray _ _ _ _ = error "bug: not a device array"

makeHostDataType ::
  forall a. (EdhXchg a, Typeable a) => DataTypeIdent -> a -> DataType
makeHostDataType !dti !def'val =
  DataType
    dti
    (HostDataType def'val)
    createArray
    growArray
    readArrayCell
    writeArrayCell
    updateArray
  where
    createArray !cap = unsafeIOToSTM (snd <$> newHostArray @a def'val cap)
    growArray (HostArray !cap !ha'') !newCap = case cast ha'' of
      Nothing -> error "bug: not a host array"
      Just (ha :: MV.IOVector a) -> unsafeIOToSTM $ do
        (ha' :: MV.IOVector a) <- MV.unsafeNew newCap
        let !cpLen = min newCap cap
        if cpLen <= 0
          then MV.set ha' def'val
          else do
            let !tgt = MV.unsafeSlice 0 cpLen ha'
                !src = MV.unsafeSlice 0 cpLen ha
                !restLen = newCap - cpLen
            MV.unsafeCopy tgt src
            when (restLen > 0) $
              MV.set (MV.unsafeSlice cpLen restLen ha') def'val
        return $ HostArray newCap ha'
    growArray _ _ = error "bug: not a host array"
    readArrayCell !ets (HostArray !cap !ha) !idx !exit =
      edhRegulateIndex ets cap idx $ \ !posIdx -> do
        !sv <- unsafeIOToSTM $ MV.unsafeRead ha posIdx
        toEdh ets sv $ \ !val -> exit val
    readArrayCell _ _ _ _ = error "bug: not a host array"
    writeArrayCell !ets (HostArray !cap !ha) !idx !val !exit =
      edhRegulateIndex ets cap idx $
        \ !posIdx -> fromEdh ets val $ \ !sv -> do
          unsafeIOToSTM $ MV.unsafeWrite ha posIdx sv
          toEdh ets sv $ \ !val' -> exit val'
    writeArrayCell _ _ _ _ _ = error "bug: not a host array"
    updateArray _ [] _ !exit = exit
    updateArray
      !ets
      ((!idx, !val) : rest'upds)
      ary@(HostArray !cap !ha)
      !exit =
        edhRegulateIndex ets cap idx $
          \ !posIdx -> fromEdh ets val $ \ !sv -> do
            unsafeIOToSTM $ MV.unsafeWrite ha posIdx sv
            updateArray ets rest'upds ary exit
    updateArray _ _ _ _ = error "bug: not a host array"

data FlatOrd where
  FlatOrd ::
    { flat'cmp'vectorized ::
        EdhThreadState ->
        FlatArray ->
        (Ordering -> Bool) ->
        EdhValue ->
        (FlatArray -> STM ()) ->
        STM (),
      flat'cmp'element'wise ::
        EdhThreadState ->
        FlatArray ->
        (Ordering -> Bool) ->
        FlatArray ->
        (FlatArray -> STM ()) ->
        STM ()
    } ->
    FlatOrd

deviceDataOrdering ::
  forall a. (Ord a, Storable a, Typeable a, EdhXchg a) => FlatOrd
deviceDataOrdering = FlatOrd vecCmp elemCmp
  where
    -- vectorized comparation, yielding a new YesNo array
    vecCmp !ets (DeviceArray !cap !fp) !cmp !v !exit =
      fromEdh @a ets v $ \ !sv ->
        (exit =<<) $
          unsafeIOToSTM $
            withForeignPtr (castForeignPtr fp) $ \ !p ->
              do
                !rp <- callocArray @YesNo cap
                !rfp <- newForeignPtr finalizerFree rp
                let go i
                      | i >= cap =
                        return $ DeviceArray cap rfp
                    go i = do
                      !ev <- peekElemOff p i
                      pokeElemOff rp i $
                        if cmp $ compare @a ev sv then 1 else 0
                      go (i + 1)
                go 0
    vecCmp _ _ _ _ _ = error "bug: not a device array"
    -- element-wise comparation, yielding a new YesNo array
    elemCmp
      _ets
      (DeviceArray !cap1 !fp1)
      !cmp
      (DeviceArray !cap2 !fp2)
      !exit =
        (exit =<<) $
          unsafeIOToSTM $
            withForeignPtr (castForeignPtr fp1) $
              \(p1 :: Ptr a) ->
                withForeignPtr (castForeignPtr fp2) $ \(p2 :: Ptr a) -> do
                  !rp <- callocArray @YesNo rcap
                  !rfp <- newForeignPtr finalizerFree rp
                  let go i
                        | i >= rcap =
                          return $ DeviceArray rcap rfp
                      go i = do
                        !ev1 <- peekElemOff p1 i
                        !ev2 <- peekElemOff p2 i
                        pokeElemOff rp i $
                          if cmp $ compare ev1 ev2 then 1 else 0
                        go (i + 1)
                  go 0
        where
          !rcap = min cap1 cap2
    elemCmp _ _ _ _ _ = error "bug: not a device array"

hostDataOrdering :: forall a. (Ord a, Typeable a, EdhXchg a) => FlatOrd
hostDataOrdering = FlatOrd vecCmp elemCmp
  where
    -- vectorized comparation, yielding a new YesNo array
    vecCmp !ets (HostArray !cap !ha'') !cmp !v !exit = case cast ha'' of
      Nothing -> error "bug: host array dtype mismatch"
      Just (ha :: MV.IOVector a) -> fromEdh @a ets v $ \ !sv ->
        (exit =<<) $
          unsafeIOToSTM $ do
            !rp <- callocArray @YesNo cap
            !rfp <- newForeignPtr finalizerFree rp
            let go i
                  | i >= cap =
                    return $ DeviceArray cap rfp
                go i = do
                  !ev <- MV.unsafeRead ha i
                  pokeElemOff rp i $ if cmp $ compare @a ev sv then 1 else 0
                  go (i + 1)
            go 0
    vecCmp _ _ _ _ _ = error "bug: not a host array"
    -- element-wise comparation, yielding a new YesNo array
    elemCmp _ets (HostArray !cap1 !ha1'') !cmp (HostArray !cap2 !ha2'') !exit =
      case cast ha1'' of
        Nothing -> error "bug: host array dtype mismatch"
        Just (ha1 :: MV.IOVector a) -> case cast ha2'' of
          Nothing -> error "bug: host array dtype mismatch"
          Just (ha2 :: MV.IOVector a) -> (exit =<<) $
            unsafeIOToSTM $ do
              !rp <- callocArray @YesNo rcap
              !rfp <- newForeignPtr finalizerFree rp
              let go i
                    | i >= rcap =
                      return $ DeviceArray rcap rfp
                  go i = do
                    !ev1 <- MV.unsafeRead ha1 i
                    !ev2 <- MV.unsafeRead ha2 i
                    pokeElemOff rp i $ if cmp $ compare ev1 ev2 then 1 else 0
                    go (i + 1)
              go 0
      where
        !rcap = min cap1 cap2
    elemCmp _ _ _ _ _ = error "bug: not a host array"

edhDataOrdering :: FlatOrd
edhDataOrdering = FlatOrd vecCmp elemCmp
  where
    -- vectorized comparation, yielding a new YesNo array
    vecCmp !ets (HostArray !cap !ha'') !cmp !sv !exit = case cast ha'' of
      Nothing -> error "bug: host array dtype mismatch"
      Just (ha :: MV.IOVector EdhValue) -> do
        !rp <- unsafeIOToSTM $ callocArray @YesNo cap
        !rfp <- unsafeIOToSTM $ newForeignPtr finalizerFree rp
        let go i | i >= cap = exit $ DeviceArray cap rfp
            go i = do
              !ev <- unsafeIOToSTM $ MV.unsafeRead ha i
              edhCompareValue ets ev sv $ \ !maybeOrd -> do
                case maybeOrd of
                  Nothing -> unsafeIOToSTM $ pokeElemOff rp i 0
                  Just !ord ->
                    unsafeIOToSTM $ pokeElemOff rp i $ if cmp ord then 1 else 0
                go (i + 1)
        go 0
    vecCmp _ _ _ _ _ = error "bug: not a host array"
    -- element-wise comparation, yielding a new YesNo array
    elemCmp !ets (HostArray !cap1 !ha1'') !cmp (HostArray !cap2 !ha2'') !exit =
      case cast ha1'' of
        Nothing -> error "bug: host array dtype mismatch"
        Just (ha1 :: MV.IOVector EdhValue) -> case cast ha2'' of
          Nothing -> error "bug: host array dtype mismatch"
          Just (ha2 :: MV.IOVector EdhValue) -> do
            !rp <- unsafeIOToSTM $ callocArray @YesNo rcap
            !rfp <- unsafeIOToSTM $ newForeignPtr finalizerFree rp
            let go i | i >= rcap = exit $ DeviceArray rcap rfp
                go i = do
                  !ev1 <- unsafeIOToSTM $ MV.unsafeRead ha1 i
                  !ev2 <- unsafeIOToSTM $ MV.unsafeRead ha2 i
                  edhCompareValue ets ev1 ev2 $ \ !maybeOrd -> do
                    case maybeOrd of
                      Nothing -> unsafeIOToSTM $ pokeElemOff rp i 0
                      Just !ord ->
                        unsafeIOToSTM $
                          pokeElemOff rp i $ if cmp ord then 1 else 0
                    go (i + 1)
            go 0
      where
        !rcap = min cap1 cap2
    elemCmp _ _ _ _ _ = error "bug: not a host array"

resolveDataComparator ::
  EdhThreadState ->
  DataTypeIdent ->
  FlatArray ->
  (FlatOrd -> STM ()) ->
  STM ()
resolveDataComparator !ets !dti !fa =
  resolveDataComparator' ets dti fa $
    throwEdh ets UsageError $
      "ordering not supported by dtype: " <> dti

resolveDataComparator' ::
  EdhThreadState ->
  DataTypeIdent ->
  FlatArray ->
  STM () ->
  (FlatOrd -> STM ()) ->
  STM ()
resolveDataComparator' !ets !dti _ !naExit !exit = runEdhTx ets $
  behaveEdhEffect' (AttrByName $ "__DataComparator_" <> dti <> "__") $ \case
    Just (EdhObject !foObj) -> case edh'obj'store foObj of
      HostStore !dd -> case fromDynamic dd of
        Nothing -> const naExit
        Just (fo :: FlatOrd) -> const $ exit fo
      _ -> const naExit
    _ -> const naExit

data FlatOp where
  FlatOp ::
    { flat'extract'yesno ::
        EdhThreadState ->
        FlatArray ->
        FlatArray ->
        ((FlatArray, Int) -> STM ()) ->
        STM (),
      flat'extract'fancy ::
        EdhThreadState ->
        FlatArray ->
        FlatArray ->
        (FlatArray -> STM ()) ->
        STM (),
      flat'op'fold ::
        EdhThreadState ->
        FlatArray ->
        Dynamic ->
        EdhValue ->
        (EdhValue -> STM ()) ->
        STM (),
      flat'op'scan ::
        EdhThreadState ->
        FlatArray ->
        Dynamic ->
        EdhValue ->
        (FlatArray -> STM ()) ->
        STM (),
      flat'op'vectorized ::
        EdhThreadState ->
        FlatArray ->
        Dynamic ->
        EdhValue ->
        (FlatArray -> STM ()) ->
        STM (),
      flat'op'element'wise ::
        EdhThreadState ->
        FlatArray ->
        Dynamic ->
        FlatArray ->
        (FlatArray -> STM ()) ->
        STM (),
      flat'inp'vectorized ::
        EdhThreadState ->
        FlatArray ->
        Dynamic ->
        EdhValue ->
        STM () ->
        STM (),
      flat'inp'vectorized'slice ::
        EdhThreadState ->
        (Int, Int, Int) ->
        FlatArray ->
        Dynamic ->
        EdhValue ->
        STM () ->
        STM (),
      flat'inp'vectorized'masked ::
        EdhThreadState ->
        FlatArray ->
        FlatArray ->
        Dynamic ->
        EdhValue ->
        STM () ->
        STM (),
      flat'inp'vectorized'fancy ::
        EdhThreadState ->
        FlatArray ->
        FlatArray ->
        Dynamic ->
        EdhValue ->
        STM () ->
        STM (),
      flat'inp'element'wise ::
        EdhThreadState ->
        FlatArray ->
        Dynamic ->
        FlatArray ->
        STM () ->
        STM (),
      flat'inp'element'wise'slice ::
        EdhThreadState ->
        (Int, Int, Int) ->
        FlatArray ->
        Dynamic ->
        FlatArray ->
        STM () ->
        STM (),
      flat'inp'element'wise'masked ::
        EdhThreadState ->
        FlatArray ->
        FlatArray ->
        Dynamic ->
        FlatArray ->
        STM () ->
        STM (),
      flat'inp'element'wise'fancy ::
        EdhThreadState ->
        FlatArray ->
        FlatArray ->
        Dynamic ->
        FlatArray ->
        STM () ->
        STM ()
    } ->
    FlatOp

deviceDataOperations ::
  forall a. (EdhXchg a, Storable a, Typeable a) => FlatOp
deviceDataOperations =
  FlatOp
    vecExtractBool
    vecExtractFancy
    foldOp
    scanOp
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
    vecExtractBool
      _ets
      (DeviceArray !mcap !mfp)
      (DeviceArray _cap !fp)
      !exit =
        (exit =<<) $
          unsafeIOToSTM $
            withForeignPtr (castForeignPtr mfp) $
              \(mp :: Ptr YesNo) ->
                withForeignPtr (castForeignPtr fp) $ \(p :: Ptr a) -> do
                  !rp <- callocArray mcap
                  !rfp <- newForeignPtr @a finalizerFree rp
                  let go i ri
                        | i >= mcap =
                          return (DeviceArray mcap rfp, ri)
                      go i ri = do
                        !mv <- peekElemOff mp i
                        if mv /= 0
                          then do
                            peekElemOff p i >>= pokeElemOff rp ri
                            go (i + 1) (ri + 1)
                          else go (i + 1) ri
                  go 0 0
    vecExtractBool _ _ _ _ = error "bug: not a device array"
    -- vectorized data extraction with a fancy index, yielding a new array
    vecExtractFancy
      !ets
      (DeviceArray !icap !ifp)
      (DeviceArray !cap !fp)
      !exit =
        do
          !result <- unsafeIOToSTM $
            withForeignPtr fp $ \ !p ->
              withForeignPtr (castForeignPtr ifp) $ \(ip :: Ptr Int) -> do
                !rp <- callocArray icap
                !rfp <- newForeignPtr finalizerFree rp
                let go i
                      | i >= icap =
                        return $ Right $ DeviceArray icap rfp
                    go i = do
                      !idx <- peekElemOff ip i
                      if idx < 0 || idx >= cap
                        then return $ Left idx
                        else do
                          peekElemOff p idx >>= pokeElemOff rp i
                          go (i + 1)
                go 0
          case result of
            Left !badIdx ->
              throwEdh ets EvalError $
                "fancy index out of bounds: "
                  <> T.pack (show badIdx)
                  <> " vs "
                  <> T.pack (show cap)
            Right !rtnAry -> exit rtnAry
    vecExtractFancy _ _ _ _ = error "bug: not a device array"
    -- fold operation, returning the cumulated scalar
    foldOp !ets (DeviceArray !cap !fp) !dop !v !exit =
      case fromDynamic dop of
        Nothing -> error "bug: dtype op type mismatch"
        Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv -> do
          !rv <- unsafeIOToSTM $
            withForeignPtr (castForeignPtr fp) $
              \(p :: Ptr a) -> do
                let go i cv
                      | i >= cap =
                        return cv
                    go i cv = do
                      !ev <- peekElemOff p i
                      let !nv = op cv ev
                      go (i + 1) nv
                go 0 sv
          toEdh ets rv exit
    foldOp _ _ _ _ _ = error "bug: not a device array"
    -- scan operation, yielding a new array
    scanOp !ets (DeviceArray !cap !fp) !dop !v !exit =
      case fromDynamic dop of
        Nothing -> error "bug: dtype op type mismatch"
        Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv ->
          (exit =<<) $
            unsafeIOToSTM $
              withForeignPtr (castForeignPtr fp) $
                \(p :: Ptr a) -> do
                  !rp <- callocArray cap
                  !rfp <- newForeignPtr finalizerFree rp
                  let go i _cv
                        | i >= cap =
                          return $ DeviceArray cap rfp
                      go i cv = do
                        !ev <- peekElemOff p i
                        let !nv = op cv ev
                        pokeElemOff rp i nv
                        go (i + 1) nv
                  go 0 sv
    scanOp _ _ _ _ _ = error "bug: not a device array"
    -- vectorized operation, yielding a new array
    vecOp !ets (DeviceArray !cap !fp) !dop !v !exit =
      case fromDynamic dop of
        Nothing -> error "bug: dtype op type mismatch"
        Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv ->
          (exit =<<) $
            unsafeIOToSTM $
              withForeignPtr (castForeignPtr fp) $
                \(p :: Ptr a) -> do
                  !rp <- callocArray cap
                  !rfp <- newForeignPtr finalizerFree rp
                  let go i
                        | i >= cap =
                          return $ DeviceArray cap rfp
                      go i = do
                        !ev <- peekElemOff p i
                        pokeElemOff rp i $ op ev sv
                        go (i + 1)
                  go 0
    vecOp _ _ _ _ _ = error "bug: not a device array"
    -- element-wise operation, yielding a new array
    elemOp
      _ets
      (DeviceArray !cap1 !fp1)
      !dop
      (DeviceArray !cap2 !fp2)
      !exit =
        case fromDynamic dop of
          Nothing -> error "bug: dtype op type mismatch"
          Just (op :: a -> a -> a) ->
            (exit =<<) $
              unsafeIOToSTM $
                withForeignPtr (castForeignPtr fp1) $
                  \(p1 :: Ptr a) ->
                    withForeignPtr (castForeignPtr fp2) $ \(p2 :: Ptr a) -> do
                      !rp <- callocArray rcap
                      !rfp <- newForeignPtr finalizerFree rp
                      let go i
                            | i >= rcap =
                              return $ DeviceArray rcap rfp
                          go i = do
                            !ev1 <- peekElemOff p1 i
                            !ev2 <- peekElemOff p2 i
                            pokeElemOff rp i $ op ev1 ev2
                            go (i + 1)
                      go 0
        where
          !rcap = min cap1 cap2
    elemOp _ _ _ _ _ = error "bug: not a device array"
    -- vectorized operation, inplace modifying the array
    vecInp !ets (DeviceArray !cap !fp) !dop !v !exit =
      case fromDynamic dop of
        Nothing -> error "bug: dtype op type mismatch"
        Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv ->
          (>> exit) $
            unsafeIOToSTM $
              withForeignPtr (castForeignPtr fp) $
                \(p :: Ptr a) -> do
                  let go i | i >= cap = return ()
                      go i = do
                        !ev <- peekElemOff p i
                        pokeElemOff p i $ op ev sv
                        go (i + 1)
                  go 0
    vecInp _ _ _ _ _ = error "bug: not a device array"
    -- vectorized operation, inplace modifying the array, with a slice spec
    vecInpSlice
      !ets
      (!start, !stop, !step)
      (DeviceArray _cap !fp)
      !dop
      !v
      !exit =
        case fromDynamic dop of
          Nothing -> error "bug: dtype op type mismatch"
          Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv ->
            (>> exit) $
              unsafeIOToSTM $
                withForeignPtr (castForeignPtr fp) $
                  \(p :: Ptr a) -> do
                    let (q, r) = quotRem (stop - start) step
                        !len = if r == 0 then abs q else 1 + abs q
                    let go _ i | i >= len = return ()
                        go n i = do
                          !ev <- peekElemOff p n
                          pokeElemOff p n $ op ev sv
                          go (n + step) (i + 1)
                    go start 0
    vecInpSlice _ _ _ _ _ _ = error "bug: not a device array"
    -- vectorized operation, inplace modifying the array, with a yesno mask
    vecInpMasked
      !ets
      (DeviceArray _mcap !mfp)
      (DeviceArray !cap !fp)
      !dop
      !v
      !exit =
        case fromDynamic dop of
          Nothing -> error "bug: dtype op type mismatch"
          Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv ->
            (>> exit) $
              unsafeIOToSTM $
                withForeignPtr (castForeignPtr mfp) $
                  \(mp :: Ptr YesNo) ->
                    withForeignPtr (castForeignPtr fp) $ \(p :: Ptr a) -> do
                      let go i | i >= cap = return ()
                          go i = do
                            !mv <- peekElemOff mp i
                            when (mv /= 0) $ do
                              !ev <- peekElemOff p i
                              pokeElemOff p i $ op ev sv
                            go (i + 1)
                      go 0
    vecInpMasked _ _ _ _ _ _ = error "bug: not a device array"
    -- vectorized operation, inplace modifying the array, with a fancy index
    vecInpFancy
      !ets
      (DeviceArray !icap !ifp)
      (DeviceArray !cap !fp)
      !dop
      !v
      !exit =
        case fromDynamic dop of
          Nothing -> error "bug: dtype op type mismatch"
          Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv -> do
            !badIdx <-
              unsafeIOToSTM $
                withForeignPtr (castForeignPtr ifp) $
                  \(ip :: Ptr Int) ->
                    withForeignPtr (castForeignPtr fp) $ \(p :: Ptr a) -> do
                      let go i | i >= icap = return 0
                          go i =
                            peekElemOff ip i >>= \ !idx ->
                              if idx < 0 || idx >= cap
                                then return idx
                                else do
                                  !ev <- peekElemOff p idx
                                  pokeElemOff p idx $ op ev sv
                                  go (i + 1)
                      go 0
            if badIdx == 0
              then exit
              else
                throwEdh ets EvalError $
                  "fancy index out of bounds: "
                    <> T.pack (show badIdx)
                    <> " vs "
                    <> T.pack (show cap)
    vecInpFancy _ _ _ _ _ _ = error "bug: not a device array"
    -- element-wise operation, inplace modifying array
    elemInp
      _ets
      (DeviceArray !cap1 !fp1)
      !dop
      (DeviceArray !cap2 !fp2)
      !exit =
        case fromDynamic dop of
          Nothing -> error "bug: dtype op type mismatch"
          Just (op :: a -> a -> a) ->
            (>> exit) $
              unsafeIOToSTM $
                withForeignPtr (castForeignPtr fp1) $
                  \(p1 :: Ptr a) ->
                    withForeignPtr (castForeignPtr fp2) $ \(p2 :: Ptr a) -> do
                      let go i | i >= rcap = return ()
                          go i = do
                            !ev1 <- peekElemOff p1 i
                            !ev2 <- peekElemOff p2 i
                            pokeElemOff p1 i $ op ev1 ev2
                            go (i + 1)
                      go 0
        where
          !rcap = min cap1 cap2
    elemInp _ _ _ _ _ = error "bug: not a device array"
    -- element-wise operation, inplace modifying array, with a slice spec
    elemInpSlice
      _ets
      (!start, !stop, !step)
      (DeviceArray _cap1 !fp1)
      !dop
      (DeviceArray !cap2 !fp2)
      !exit =
        case fromDynamic dop of
          Nothing -> error "bug: dtype op type mismatch"
          Just (op :: a -> a -> a) ->
            (>> exit) $
              unsafeIOToSTM $
                withForeignPtr (castForeignPtr fp1) $
                  \(p1 :: Ptr a) ->
                    withForeignPtr (castForeignPtr fp2) $ \(p2 :: Ptr a) -> do
                      let (q, r) = quotRem (stop - start) step
                          !len = min cap2 $ if r == 0 then abs q else 1 + abs q
                      let go _ i | i >= len = return ()
                          go n i = do
                            !ev1 <- peekElemOff p1 n
                            !ev2 <- peekElemOff p2 i
                            pokeElemOff p1 n $ op ev1 ev2
                            go (n + step) (i + 1)
                      go start 0
    elemInpSlice _ _ _ _ _ _ = error "bug: not a device array"
    -- element-wise operation, inplace modifying array, with a yesno mask
    elemInpMasked
      _ets
      (DeviceArray _mcap !mfp)
      (DeviceArray !cap1 !fp1)
      !dop
      (DeviceArray !cap2 !fp2)
      !exit =
        case fromDynamic dop of
          Nothing -> error "bug: dtype op type mismatch"
          Just (op :: a -> a -> a) ->
            (>> exit) $
              unsafeIOToSTM $
                withForeignPtr (castForeignPtr mfp) $
                  \(mp :: Ptr YesNo) ->
                    withForeignPtr (castForeignPtr fp1) $ \(p1 :: Ptr a) ->
                      withForeignPtr (castForeignPtr fp2) $ \(p2 :: Ptr a) -> do
                        let go i | i >= rcap = return ()
                            go i = do
                              !mv <- peekElemOff mp i
                              when (mv /= 0) $ do
                                !ev1 <- peekElemOff p1 i
                                !ev2 <- peekElemOff p2 i
                                pokeElemOff p1 i $ op ev1 ev2
                              go (i + 1)
                        go 0
        where
          !rcap = min cap1 cap2
    elemInpMasked _ _ _ _ _ _ = error "bug: not a device array"
    -- element-wise operation, inplace modifying array, with a fancy index
    elemInpFancy
      !ets
      (DeviceArray !icap !ifp)
      (DeviceArray !cap1 !fp1)
      !dop
      (DeviceArray !cap2 !fp2)
      !exit =
        case fromDynamic dop of
          Nothing -> error "bug: dtype op type mismatch"
          Just (op :: a -> a -> a) -> do
            !badIdx <-
              unsafeIOToSTM $
                withForeignPtr (castForeignPtr ifp) $
                  \(ip :: Ptr Int) ->
                    withForeignPtr (castForeignPtr fp1) $ \(p1 :: Ptr a) ->
                      withForeignPtr (castForeignPtr fp2) $ \(p2 :: Ptr a) -> do
                        let len = min icap cap2
                        let go i | i >= len = return 0
                            go i =
                              peekElemOff ip i >>= \ !idx ->
                                if idx < 0 || idx >= cap1
                                  then return idx
                                  else do
                                    !ev1 <- peekElemOff p1 idx
                                    !ev2 <- peekElemOff p2 i
                                    pokeElemOff p1 idx $ op ev1 ev2
                                    go (i + 1)
                        go 0
            if badIdx == 0
              then exit
              else
                throwEdh ets EvalError $
                  "fancy index out of bounds: "
                    <> T.pack (show badIdx)
                    <> " vs "
                    <> T.pack (show cap1)
    elemInpFancy _ _ _ _ _ _ = error "bug: not a device array"

hostDataOperations :: forall a. (EdhXchg a, Typeable a) => a -> FlatOp
hostDataOperations !def'val =
  FlatOp
    vecExtractBool
    vecExtractFancy
    foldOp
    scanOp
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
    vecExtractBool
      _ets
      (DeviceArray !mcap !mfp)
      (HostArray _cap !ha'')
      !exit =
        case cast ha'' of
          Nothing -> error "bug: host array dtype mismatch"
          Just (ha :: MV.IOVector a) ->
            (exit =<<) $
              unsafeIOToSTM $
                withForeignPtr (castForeignPtr mfp) $
                  \(mp :: Ptr YesNo) -> do
                    !ha' <- MV.unsafeNew mcap
                    let go i ri | i >= mcap = do
                          MV.set (MV.unsafeSlice ri (mcap - ri) ha') def'val
                          return (HostArray mcap ha', ri)
                        go i ri = do
                          !mv <- peekElemOff mp i
                          if mv /= 0
                            then do
                              MV.unsafeRead ha i >>= MV.unsafeWrite ha' ri
                              go (i + 1) (ri + 1)
                            else go (i + 1) ri
                    go 0 0
    vecExtractBool _ _ _ _ = error "bug: not a host array"
    -- vectorized data extraction with a fancy index, yielding a new array
    vecExtractFancy
      !ets
      (DeviceArray !icap !ifp)
      (HostArray !cap !ha'')
      !exit =
        case cast ha'' of
          Nothing -> error "bug: host array dtype mismatch"
          Just (ha :: MV.IOVector a) -> do
            !result <-
              unsafeIOToSTM $
                withForeignPtr (castForeignPtr ifp) $
                  \(ip :: Ptr Int) -> do
                    !ha' <- MV.unsafeNew icap
                    let go i | i >= icap = return $ Right $ HostArray icap ha'
                        go i = do
                          !idx <- peekElemOff ip i
                          if idx < 0 || idx >= cap
                            then return $ Left idx
                            else do
                              MV.read ha idx >>= MV.unsafeWrite ha' i
                              go (i + 1)
                    go 0
            case result of
              Left !badIdx ->
                throwEdh ets EvalError $
                  "fancy index out of bounds: "
                    <> T.pack (show badIdx)
                    <> " vs "
                    <> T.pack (show cap)
              Right !rtnAry -> exit rtnAry
    vecExtractFancy _ _ _ _ = error "bug: not a host array"
    -- fold operation, returning the cumulated scalar
    foldOp !ets (HostArray !cap !ha'') !dop !v !exit = case cast ha'' of
      Nothing -> error "bug: host array dtype mismatch"
      Just (ha :: MV.IOVector a) -> case fromDynamic dop of
        Nothing -> error "bug: dtype op type mismatch"
        Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv -> do
          !rv <- unsafeIOToSTM $ do
            let go i cv | i >= cap = return cv
                go i cv = do
                  !ev <- MV.unsafeRead ha i
                  let !nv = op cv ev
                  go (i + 1) nv
            go 0 sv
          toEdh ets rv exit
    foldOp _ _ _ _ _ = error "bug: not a host array"
    -- scan operation, yielding a new array
    scanOp !ets (HostArray !cap !ha'') !dop !v !exit = case cast ha'' of
      Nothing -> error "bug: host array dtype mismatch"
      Just (ha :: MV.IOVector a) -> case fromDynamic dop of
        Nothing -> error "bug: dtype op type mismatch"
        Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv ->
          (exit =<<) $
            unsafeIOToSTM $ do
              !ha' <- MV.unsafeNew cap
              let go i _cv | i >= cap = return $ HostArray cap ha'
                  go i cv = do
                    !ev <- MV.unsafeRead ha i
                    let !nv = op cv ev
                    MV.unsafeWrite ha' i nv
                    go (i + 1) nv
              go 0 sv
    scanOp _ _ _ _ _ = error "bug: not a host array"
    -- vectorized operation, yielding a new array
    vecOp !ets (HostArray !cap !ha'') !dop !v !exit = case cast ha'' of
      Nothing -> error "bug: host array dtype mismatch"
      Just (ha :: MV.IOVector a) -> case fromDynamic dop of
        Nothing -> error "bug: dtype op type mismatch"
        Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv ->
          (exit =<<) $
            unsafeIOToSTM $ do
              !ha' <- MV.unsafeNew cap
              let go i | i >= cap = return $ HostArray cap ha'
                  go i = do
                    !ev <- MV.unsafeRead ha i
                    MV.unsafeWrite ha' i $ op ev sv
                    go (i + 1)
              go 0
    vecOp _ _ _ _ _ = error "bug: not a host array"
    -- element-wise operation, yielding a new array
    elemOp _ets (HostArray !cap1 !ha''1) !dop (HostArray !cap2 !ha''2) !exit =
      case cast ha''1 of
        Nothing -> error "bug: host array dtype mismatch"
        Just (ha1 :: MV.IOVector a) -> case cast ha''2 of
          Nothing -> error "bug: host array dtype mismatch"
          Just (ha2 :: MV.IOVector a) -> case fromDynamic dop of
            Nothing -> error "bug: dtype op type mismatch"
            Just (op :: a -> a -> a) -> (exit =<<) $
              unsafeIOToSTM $ do
                !ha' <- MV.unsafeNew rcap
                let go i | i >= rcap = return $ HostArray rcap ha'
                    go i = do
                      !ev1 <- MV.unsafeRead ha1 i
                      !ev2 <- MV.unsafeRead ha2 i
                      MV.unsafeWrite ha' i $ op ev1 ev2
                      go (i + 1)
                go 0
      where
        !rcap = min cap1 cap2
    elemOp _ _ _ _ _ = error "bug: not a host array"
    -- vectorized operation, inplace modifying the array
    vecInp !ets (HostArray !cap !ha'') !dop !v !exit = case cast ha'' of
      Nothing -> error "bug: host array dtype mismatch"
      Just (ha :: MV.IOVector a) -> case fromDynamic dop of
        Nothing -> error "bug: dtype op type mismatch"
        Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv ->
          (>> exit) $
            unsafeIOToSTM $ do
              let go i | i >= cap = return ()
                  go i = do
                    !ev <- MV.unsafeRead ha i
                    MV.unsafeWrite ha i $ op ev sv
                    go (i + 1)
              go 0
    vecInp _ _ _ _ _ = error "bug: not a host array"
    -- vectorized operation, inplace modifying the array, with a slice spec
    vecInpSlice
      !ets
      (!start, !stop, !step)
      (HostArray _cap !ha'')
      !dop
      !v
      !exit =
        case cast ha'' of
          Nothing -> error "bug: host array dtype mismatch"
          Just (ha :: MV.IOVector a) -> case fromDynamic dop of
            Nothing -> error "bug: dtype op type mismatch"
            Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv ->
              (>> exit) $
                unsafeIOToSTM $ do
                  let (q, r) = quotRem (stop - start) step
                      !len = if r == 0 then abs q else 1 + abs q
                  let go _ i | i >= len = return ()
                      go n i = do
                        !ev <- MV.unsafeRead ha n
                        MV.unsafeWrite ha n $ op ev sv
                        go (n + step) (i + 1)
                  go start 0
    vecInpSlice _ _ _ _ _ _ = error "bug: not a host array"
    -- vectorized operation, inplace modifying the array, with a yesno mask
    vecInpMasked
      !ets
      (DeviceArray _mcap !mfp)
      (HostArray !cap !ha'')
      !dop
      !v
      !exit =
        case cast ha'' of
          Nothing -> error "bug: host array dtype mismatch"
          Just (ha :: MV.IOVector a) -> case fromDynamic dop of
            Nothing -> error "bug: dtype op type mismatch"
            Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv ->
              (>> exit) $
                unsafeIOToSTM $
                  withForeignPtr (castForeignPtr mfp) $
                    \(mp :: Ptr YesNo) -> do
                      let go i | i >= cap = return ()
                          go i = do
                            !mv <- peekElemOff mp i
                            when (mv /= 0) $ do
                              !ev <- MV.unsafeRead ha i
                              MV.unsafeWrite ha i $ op ev sv
                            go (i + 1)
                      go 0
    vecInpMasked _ _ _ _ _ _ = error "bug: not a host array"
    -- vectorized operation, inplace modifying the array, with a fancy index
    vecInpFancy
      !ets
      (DeviceArray !icap !ifp)
      (HostArray !cap !ha'')
      !dop
      !v
      !exit =
        case cast ha'' of
          Nothing -> error "bug: host array dtype mismatch"
          Just (ha :: MV.IOVector a) -> case fromDynamic dop of
            Nothing -> error "bug: dtype op type mismatch"
            Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv -> do
              !badIdx <-
                unsafeIOToSTM $
                  withForeignPtr (castForeignPtr ifp) $
                    \(ip :: Ptr Int) -> do
                      let go i | i >= icap = return 0
                          go i =
                            peekElemOff ip i >>= \ !idx ->
                              if idx < 0 || idx >= cap
                                then return idx
                                else do
                                  !ev <- MV.unsafeRead ha idx
                                  MV.unsafeWrite ha idx $ op ev sv
                                  go (i + 1)
                      go 0
              if badIdx == 0
                then exit
                else
                  throwEdh ets EvalError $
                    "fancy index out of bounds: "
                      <> T.pack (show badIdx)
                      <> " vs "
                      <> T.pack (show cap)
    vecInpFancy _ _ _ _ _ _ = error "bug: not a host array"
    -- element-wise operation, inplace modifying array
    elemInp
      _ets
      (HostArray !cap1 !ha''1)
      !dop
      (HostArray !cap2 !ha''2)
      !exit =
        case cast ha''1 of
          Nothing -> error "bug: host array dtype mismatch"
          Just (ha1 :: MV.IOVector a) -> case cast ha''2 of
            Nothing -> error "bug: host array dtype mismatch"
            Just (ha2 :: MV.IOVector a) -> case fromDynamic dop of
              Nothing -> error "bug: dtype op type mismatch"
              Just (op :: a -> a -> a) -> (>> exit) $
                unsafeIOToSTM $ do
                  let go i | i >= rcap = return ()
                      go i = do
                        !ev1 <- MV.unsafeRead ha1 i
                        !ev2 <- MV.unsafeRead ha2 i
                        MV.unsafeWrite ha1 i $ op ev1 ev2
                        go (i + 1)
                  go 0
        where
          !rcap = min cap1 cap2
    elemInp _ _ _ _ _ = error "bug: not a host array"
    -- element-wise operation, inplace modifying array, with a slice spec
    elemInpSlice
      _ets
      (!start, !stop, !step)
      (HostArray _cap1 !ha''1)
      !dop
      (HostArray !cap2 !ha''2)
      !exit =
        case cast ha''1 of
          Nothing -> error "bug: host array dtype mismatch"
          Just (ha1 :: MV.IOVector a) -> case cast ha''2 of
            Nothing -> error "bug: host array dtype mismatch"
            Just (ha2 :: MV.IOVector a) -> case fromDynamic dop of
              Nothing -> error "bug: dtype op type mismatch"
              Just (op :: a -> a -> a) -> (>> exit) $
                unsafeIOToSTM $ do
                  let (q, r) = quotRem (stop - start) step
                      !len = min cap2 $ if r == 0 then abs q else 1 + abs q
                  let go _ i | i >= len = return ()
                      go n i = do
                        !ev1 <- MV.unsafeRead ha1 n
                        !ev2 <- MV.unsafeRead ha2 i
                        MV.unsafeWrite ha1 n $ op ev1 ev2
                        go (n + step) (i + 1)
                  go start 0
    elemInpSlice _ _ _ _ _ _ = error "bug: not a host array"
    -- element-wise operation, inplace modifying array, with a yesno mask
    elemInpMasked
      _ets
      (DeviceArray _mcap !mfp)
      (HostArray !cap1 !ha''1)
      !dop
      (HostArray !cap2 !ha''2)
      !exit =
        case cast ha''1 of
          Nothing -> error "bug: host array dtype mismatch"
          Just (ha1 :: MV.IOVector a) -> case cast ha''2 of
            Nothing -> error "bug: host array dtype mismatch"
            Just (ha2 :: MV.IOVector a) -> case fromDynamic dop of
              Nothing -> error "bug: dtype op type mismatch"
              Just (op :: a -> a -> a) ->
                (>> exit) $
                  unsafeIOToSTM $
                    withForeignPtr (castForeignPtr mfp) $
                      \(mp :: Ptr YesNo) -> do
                        let go i | i >= rcap = return ()
                            go i = do
                              !mv <- peekElemOff mp i
                              when (mv /= 0) $ do
                                !ev1 <- MV.unsafeRead ha1 i
                                !ev2 <- MV.unsafeRead ha2 i
                                MV.unsafeWrite ha1 i $ op ev1 ev2
                              go (i + 1)
                        go 0
        where
          !rcap = min cap1 cap2
    elemInpMasked _ _ _ _ _ _ = error "bug: not a host array"
    -- element-wise operation, inplace modifying array, with a fancy index
    elemInpFancy
      !ets
      (DeviceArray !icap !ifp)
      (HostArray !cap1 !ha''1)
      !dop
      (HostArray !cap2 !ha''2)
      !exit =
        case cast ha''1 of
          Nothing -> error "bug: host array dtype mismatch"
          Just (ha1 :: MV.IOVector a) -> case cast ha''2 of
            Nothing -> error "bug: host array dtype mismatch"
            Just (ha2 :: MV.IOVector a) -> case fromDynamic dop of
              Nothing -> error "bug: dtype op type mismatch"
              Just (op :: a -> a -> a) -> do
                !badIdx <-
                  unsafeIOToSTM $
                    withForeignPtr (castForeignPtr ifp) $
                      \(ip :: Ptr Int) -> do
                        let len = min icap cap2
                        let go i | i >= len = return 0
                            go i =
                              peekElemOff ip i >>= \ !idx ->
                                if idx < 0 || idx >= cap1
                                  then return idx
                                  else do
                                    !ev1 <- MV.unsafeRead ha1 idx
                                    !ev2 <- MV.unsafeRead ha2 i
                                    MV.unsafeWrite ha1 idx $ op ev1 ev2
                                    go (i + 1)
                        go 0
                if badIdx == 0
                  then exit
                  else
                    throwEdh ets EvalError $
                      "fancy index out of bounds: "
                        <> T.pack (show badIdx)
                        <> " vs "
                        <> T.pack (show cap1)
    elemInpFancy _ _ _ _ _ _ = error "bug: not a host array"

edhDataOperations :: EdhValue -> FlatOp
edhDataOperations !def'val =
  FlatOp
    vecExtractBool
    vecExtractFancy
    foldOp
    scanOp
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
    vecExtractBool
      _ets
      (DeviceArray !mcap !mfp)
      (HostArray _cap !ha'')
      !exit =
        case cast ha'' of
          Nothing -> error "bug: host array dtype mismatch"
          Just (ha :: MV.IOVector EdhValue) -> do
            let (mp :: Ptr YesNo) = unsafeForeignPtrToPtr (castForeignPtr mfp)
            !ha' <- unsafeIOToSTM $ MV.unsafeNew mcap
            let go i ri | i >= mcap = do
                  unsafeIOToSTM $
                    MV.set (MV.unsafeSlice ri (mcap - ri) ha') def'val
                  exit (HostArray mcap ha', ri)
                go i ri = do
                  !mv <- unsafeIOToSTM $ peekElemOff mp i
                  if mv /= 0
                    then do
                      unsafeIOToSTM $
                        MV.unsafeRead ha i >>= MV.unsafeWrite ha' ri
                      go (i + 1) (ri + 1)
                    else go (i + 1) ri
            go 0 0
    vecExtractBool _ _ _ _ = error "bug: not an Edh array"
    -- vectorized data extraction with a fancy index, yielding a new array
    vecExtractFancy
      !ets
      (DeviceArray !icap !ifp)
      (HostArray !cap !ha'')
      !exit =
        case cast ha'' of
          Nothing -> error "bug: host array dtype mismatch"
          Just (ha :: MV.IOVector EdhValue) -> do
            !ha' <- unsafeIOToSTM $ MV.unsafeNew icap
            let (ip :: Ptr Int) = unsafeForeignPtrToPtr (castForeignPtr ifp)
                go i | i >= icap = exit $ HostArray icap ha'
                go i = do
                  !idx <- unsafeIOToSTM $ peekElemOff ip i
                  if idx < 0 || idx >= cap
                    then
                      throwEdh ets EvalError $
                        "fancy index out of bounds: "
                          <> T.pack (show idx)
                          <> " vs "
                          <> T.pack (show cap)
                    else do
                      unsafeIOToSTM $ MV.read ha idx >>= MV.unsafeWrite ha' i
                      go (i + 1)
            go 0
    vecExtractFancy _ _ _ _ = error "bug: not an Edh array"
    -- fold operation, returning the cumulated scalar
    foldOp !ets (HostArray !cap !ha'') !dop !v !exit = case cast ha'' of
      Nothing -> error "bug: host array dtype mismatch"
      Just (ha :: MV.IOVector EdhValue) -> case fromDynamic dop of
        Nothing -> error "bug: dtype op type mismatch"
        Just (op :: EdhValue -> EdhValue -> EdhHostProc) -> do
          !ha' <- unsafeIOToSTM $ MV.unsafeNew cap
          let go i cv | i >= cap = exit cv
              go i cv = do
                !ev <- unsafeIOToSTM $ MV.unsafeRead ha i
                runEdhTx ets $
                  op cv ev $ \ !nv _ets -> do
                    unsafeIOToSTM $ MV.unsafeWrite ha' i nv
                    go (i + 1) nv
          go 0 v
    foldOp _ _ _ _ _ = error "bug: not an Edh array"
    -- scan operation, yielding a new array
    scanOp !ets (HostArray !cap !ha'') !dop !v !exit = case cast ha'' of
      Nothing -> error "bug: host array dtype mismatch"
      Just (ha :: MV.IOVector EdhValue) -> case fromDynamic dop of
        Nothing -> error "bug: dtype op type mismatch"
        Just (op :: EdhValue -> EdhValue -> EdhHostProc) -> do
          !ha' <- unsafeIOToSTM $ MV.unsafeNew cap
          let go i _cv | i >= cap = exit $ HostArray cap ha'
              go i cv = do
                !ev <- unsafeIOToSTM $ MV.unsafeRead ha i
                runEdhTx ets $
                  op cv ev $ \ !nv _ets -> do
                    unsafeIOToSTM $ MV.unsafeWrite ha' i nv
                    go (i + 1) nv
          go 0 v
    scanOp _ _ _ _ _ = error "bug: not an Edh array"
    -- vectorized operation, yielding a new array
    vecOp !ets (HostArray !cap !ha'') !dop !v !exit = case cast ha'' of
      Nothing -> error "bug: host array dtype mismatch"
      Just (ha :: MV.IOVector EdhValue) -> case fromDynamic dop of
        Nothing -> error "bug: dtype op type mismatch"
        Just (op :: EdhValue -> EdhValue -> EdhHostProc) -> do
          !ha' <- unsafeIOToSTM $ MV.unsafeNew cap
          let go i | i >= cap = exit $ HostArray cap ha'
              go i = do
                !ev <- unsafeIOToSTM $ MV.unsafeRead ha i
                runEdhTx ets $
                  op ev v $ \ !rv _ets -> do
                    unsafeIOToSTM $ MV.unsafeWrite ha' i rv
                    go (i + 1)
          go 0
    vecOp _ _ _ _ _ = error "bug: not an Edh array"
    -- element-wise operation, yielding a new array
    elemOp !ets (HostArray !cap1 !ha''1) !dop (HostArray !cap2 !ha''2) !exit =
      case cast ha''1 of
        Nothing -> error "bug: host array dtype mismatch"
        Just (ha1 :: MV.IOVector EdhValue) -> case cast ha''2 of
          Nothing -> error "bug: host array dtype mismatch"
          Just (ha2 :: MV.IOVector EdhValue) -> case fromDynamic dop of
            Nothing -> error "bug: dtype op type mismatch"
            Just (op :: EdhValue -> EdhValue -> EdhHostProc) -> do
              !ha' <- unsafeIOToSTM $ MV.unsafeNew rcap
              let go i | i >= rcap = exit $ HostArray rcap ha'
                  go i = do
                    !ev1 <- unsafeIOToSTM $ MV.unsafeRead ha1 i
                    !ev2 <- unsafeIOToSTM $ MV.unsafeRead ha2 i
                    runEdhTx ets $
                      op ev1 ev2 $ \ !rv _ets -> do
                        unsafeIOToSTM $ MV.unsafeWrite ha' i rv
                        go (i + 1)
              go 0
      where
        !rcap = min cap1 cap2
    elemOp _ _ _ _ _ = error "bug: not an Edh array"
    -- vectorized operation, inplace modifying the array
    vecInp !ets (HostArray !cap !ha'') !dop !v !exit = case cast ha'' of
      Nothing -> error "bug: host array dtype mismatch"
      Just (ha :: MV.IOVector EdhValue) -> case fromDynamic dop of
        Nothing -> error "bug: dtype op type mismatch"
        Just (op :: EdhValue -> EdhValue -> EdhHostProc) ->
          fromEdh ets v $ \ !sv -> do
            let go i | i >= cap = exit
                go i = do
                  !ev <- unsafeIOToSTM $ MV.unsafeRead ha i
                  runEdhTx ets $
                    op ev sv $ \ !rv _ets -> do
                      unsafeIOToSTM $ MV.unsafeWrite ha i rv
                      go (i + 1)
            go 0
    vecInp _ _ _ _ _ = error "bug: not an Edh array"
    -- vectorized operation, inplace modifying the array, with a slice spec
    vecInpSlice
      !ets
      (!start, !stop, !step)
      (HostArray _cap !ha'')
      !dop
      !v
      !exit =
        case cast ha'' of
          Nothing -> error "bug: host array dtype mismatch"
          Just (ha :: MV.IOVector EdhValue) -> case fromDynamic dop of
            Nothing -> error "bug: dtype op type mismatch"
            Just (op :: EdhValue -> EdhValue -> EdhHostProc) ->
              fromEdh ets v $ \ !sv -> do
                let (q, r) = quotRem (stop - start) step
                    !len = if r == 0 then abs q else 1 + abs q
                let go _ i | i >= len = exit
                    go n i = do
                      !ev <- unsafeIOToSTM $ MV.unsafeRead ha n
                      runEdhTx ets $
                        op ev sv $ \ !rv _ets -> do
                          unsafeIOToSTM $ MV.unsafeWrite ha n rv
                          go (n + step) (i + 1)
                go start 0
    vecInpSlice _ _ _ _ _ _ = error "bug: not an Edh array"
    -- vectorized operation, inplace modifying the array, with a yesno mask
    vecInpMasked
      !ets
      (DeviceArray _cap !mfp)
      (HostArray !cap !ha'')
      !dop
      !v
      !exit =
        case cast ha'' of
          Nothing -> error "bug: host array dtype mismatch"
          Just (ha :: MV.IOVector EdhValue) -> case fromDynamic dop of
            Nothing -> error "bug: dtype op type mismatch"
            Just (op :: EdhValue -> EdhValue -> EdhHostProc) -> do
              let (mp :: Ptr YesNo) =
                    unsafeForeignPtrToPtr (castForeignPtr mfp)
                  go i | i >= cap = exit
                  go i = do
                    !mv <- unsafeIOToSTM $ peekElemOff mp i
                    if mv /= 0
                      then do
                        !ev <- unsafeIOToSTM $ MV.unsafeRead ha i
                        runEdhTx ets $
                          op ev v $ \ !rv _ets -> do
                            unsafeIOToSTM $ MV.unsafeWrite ha i rv
                            go (i + 1)
                      else go (i + 1)
              go 0
    vecInpMasked _ _ _ _ _ _ = error "bug: not an Edh array"
    -- vectorized operation, inplace modifying the array, with a fancy index
    vecInpFancy
      !ets
      (DeviceArray !icap !ifp)
      (HostArray !cap !ha'')
      !dop
      !v
      !exit =
        case cast ha'' of
          Nothing -> error "bug: host array dtype mismatch"
          Just (ha :: MV.IOVector EdhValue) -> case fromDynamic dop of
            Nothing -> error "bug: dtype op type mismatch"
            Just (op :: EdhValue -> EdhValue -> EdhHostProc) -> do
              let (ip :: Ptr Int) = unsafeForeignPtrToPtr (castForeignPtr ifp)
                  go i | i >= icap = exit
                  go i =
                    unsafeIOToSTM (peekElemOff ip i) >>= \ !idx ->
                      if idx < 0 || idx >= cap
                        then
                          throwEdh ets EvalError $
                            "fancy index out of bounds: "
                              <> T.pack (show idx)
                              <> " vs "
                              <> T.pack (show cap)
                        else do
                          !ev <- unsafeIOToSTM $ MV.unsafeRead ha idx
                          runEdhTx ets $
                            op ev v $ \ !rv _ets -> do
                              unsafeIOToSTM $ MV.unsafeWrite ha idx rv
                              go (i + 1)
              go 0
    vecInpFancy _ _ _ _ _ _ = error "bug: not an Edh array"
    -- element-wise operation, inplace modifying array
    elemInp !ets (HostArray !cap1 !ha''1) !dop (HostArray !cap2 !ha''2) !exit =
      case cast ha''1 of
        Nothing -> error "bug: host array dtype mismatch"
        Just (ha1 :: MV.IOVector EdhValue) -> case cast ha''2 of
          Nothing -> error "bug: host array dtype mismatch"
          Just (ha2 :: MV.IOVector EdhValue) -> case fromDynamic dop of
            Nothing -> error "bug: dtype op type mismatch"
            Just (op :: EdhValue -> EdhValue -> EdhHostProc) -> do
              let go i | i >= rcap = exit
                  go i = do
                    !ev1 <- unsafeIOToSTM $ MV.unsafeRead ha1 i
                    !ev2 <- unsafeIOToSTM $ MV.unsafeRead ha2 i
                    runEdhTx ets $
                      op ev1 ev2 $ \ !rv _ets -> do
                        unsafeIOToSTM $ MV.unsafeWrite ha1 i rv
                        go (i + 1)
              go 0
      where
        !rcap = min cap1 cap2
    elemInp _ _ _ _ _ = error "bug: not an Edh array"
    -- element-wise operation, inplace modifying array, with a slice spec
    elemInpSlice
      !ets
      (!start, !stop, !step)
      (HostArray _cap1 !ha''1)
      !dop
      (HostArray !cap2 !ha''2)
      !exit =
        case cast ha''1 of
          Nothing -> error "bug: host array dtype mismatch"
          Just (ha1 :: MV.IOVector EdhValue) -> case cast ha''2 of
            Nothing -> error "bug: host array dtype mismatch"
            Just (ha2 :: MV.IOVector EdhValue) -> case fromDynamic dop of
              Nothing -> error "bug: dtype op type mismatch"
              Just (op :: EdhValue -> EdhValue -> EdhHostProc) -> do
                let (q, r) = quotRem (stop - start) step
                    !len = min cap2 $ if r == 0 then abs q else 1 + abs q
                let go _ i | i >= len = exit
                    go n i = do
                      !ev1 <- unsafeIOToSTM $ MV.unsafeRead ha1 n
                      !ev2 <- unsafeIOToSTM $ MV.unsafeRead ha2 i
                      runEdhTx ets $
                        op ev1 ev2 $ \ !rv _ets -> do
                          unsafeIOToSTM $ MV.unsafeWrite ha1 n rv
                          go (n + step) (i + 1)
                go start 0
    elemInpSlice _ _ _ _ _ _ = error "bug: not an Edh array"
    -- element-wise operation, inplace modifying array, with a yesno mask
    elemInpMasked
      !ets
      (DeviceArray _mcap !mfp)
      (HostArray !cap1 !ha''1)
      !dop
      (HostArray !cap2 !ha''2)
      !exit =
        case cast ha''1 of
          Nothing -> error "bug: host array dtype mismatch"
          Just (ha1 :: MV.IOVector EdhValue) -> case cast ha''2 of
            Nothing -> error "bug: host array dtype mismatch"
            Just (ha2 :: MV.IOVector EdhValue) -> case fromDynamic dop of
              Nothing -> error "bug: dtype op type mismatch"
              Just (op :: EdhValue -> EdhValue -> EdhHostProc) -> do
                let (mp :: Ptr YesNo) =
                      unsafeForeignPtrToPtr $ castForeignPtr mfp
                    go i | i >= rcap = exit
                    go i = do
                      !mv <- unsafeIOToSTM $ peekElemOff mp i
                      if mv /= 0
                        then do
                          !ev1 <- unsafeIOToSTM $ MV.unsafeRead ha1 i
                          !ev2 <- unsafeIOToSTM $ MV.unsafeRead ha2 i
                          runEdhTx ets $
                            op ev1 ev2 $ \ !rv _ets -> do
                              unsafeIOToSTM $ MV.unsafeWrite ha1 i rv
                              go (i + 1)
                        else go (i + 1)
                go 0
        where
          !rcap = min cap1 cap2
    elemInpMasked _ _ _ _ _ _ = error "bug: not an Edh array"
    -- element-wise operation, inplace modifying array, with a fancy index
    elemInpFancy
      !ets
      (DeviceArray !icap !ifp)
      (HostArray !cap1 !ha''1)
      !dop
      (HostArray !cap2 !ha''2)
      !exit =
        case cast ha''1 of
          Nothing -> error "bug: host array dtype mismatch"
          Just (ha1 :: MV.IOVector EdhValue) -> case cast ha''2 of
            Nothing -> error "bug: host array dtype mismatch"
            Just (ha2 :: MV.IOVector EdhValue) -> case fromDynamic dop of
              Nothing -> error "bug: dtype op type mismatch"
              Just (op :: EdhValue -> EdhValue -> EdhHostProc) -> do
                let (ip :: Ptr Int) =
                      unsafeForeignPtrToPtr $ castForeignPtr ifp
                    !len = min icap cap2
                    go :: Int -> STM ()
                    go i | i >= len = exit
                    go i =
                      unsafeIOToSTM (peekElemOff ip i) >>= \ !idx ->
                        if idx < 0 || idx >= cap1
                          then
                            throwEdh ets EvalError $
                              "fancy index out of bounds: "
                                <> T.pack (show idx)
                                <> " vs "
                                <> T.pack (show cap1)
                          else do
                            !ev1 <- unsafeIOToSTM $ MV.unsafeRead ha1 idx
                            !ev2 <- unsafeIOToSTM $ MV.unsafeRead ha2 i
                            runEdhTx ets $
                              op ev1 ev2 $ \ !rv _ets -> do
                                unsafeIOToSTM $ MV.unsafeWrite ha1 idx rv
                                go (i + 1)
                go 0
    elemInpFancy _ _ _ _ _ _ = error "bug: not an Edh array"

resolveDataOperator ::
  EdhThreadState ->
  DataTypeIdent ->
  FlatArray ->
  (FlatOp -> STM ()) ->
  STM ()
resolveDataOperator !ets !dti !fa =
  resolveDataOperator' ets dti fa $
    throwEdh ets UsageError $
      "operation not supported by dtype: "
        <> dti

resolveDataOperator' ::
  EdhThreadState ->
  DataTypeIdent ->
  FlatArray ->
  STM () ->
  (FlatOp -> STM ()) ->
  STM ()
resolveDataOperator' !ets !dti _ !naExit !exit = runEdhTx ets $
  behaveEdhEffect' (AttrByName $ "__DataOperator_" <> dti <> "__") $ \case
    Just (EdhObject !foObj) -> case edh'obj'store foObj of
      HostStore !dd -> case fromDynamic dd of
        Nothing -> const naExit
        Just (fo :: FlatOp) -> const $ exit fo
      _ -> const naExit
    _ -> const naExit

resolveNumDataType ::
  EdhThreadState -> DataTypeIdent -> (NumDataType -> STM ()) -> STM ()
resolveNumDataType !ets !dti =
  resolveNumDataType' ets dti $
    throwEdh ets UsageError $
      "not an applicable numeric dtype: "
        <> dti

resolveNumDataType' ::
  EdhThreadState ->
  DataTypeIdent ->
  STM () ->
  (NumDataType -> STM ()) ->
  STM ()
resolveNumDataType' !ets !dti !naExit !exit = runEdhTx ets $
  behaveEdhEffect' (AttrByName $ "__NumDataType_" <> dti <> "__") $ \case
    Just (EdhObject !foObj) -> case edh'obj'store foObj of
      HostStore !dd -> case fromDynamic dd of
        Nothing -> const naExit
        Just (fo :: NumDataType) -> const $ exit fo
      _ -> const naExit
    _ -> const naExit

data NumDataType where
  NumDataType ::
    { flat'new'range'array ::
        EdhThreadState ->
        Int ->
        Int ->
        Int ->
        (FlatArray -> STM ()) ->
        STM (),
      flat'new'random'array ::
        EdhThreadState ->
        Int ->
        EdhValue ->
        EdhValue ->
        (FlatArray -> STM ()) ->
        STM (),
      flat'new'nonzero'array ::
        EdhThreadState ->
        FlatArray ->
        ((FlatArray, Int) -> STM ()) ->
        STM ()
    } ->
    NumDataType

deviceDataNumbering ::
  forall a.
  (Eq a, Ord a, Num a, Random a, EdhXchg a, Storable a, Typeable a) =>
  NumDataType
deviceDataNumbering = NumDataType rangeCreator randomCreator nonzeroCreator
  where
    rangeCreator _ !start !stop _ !exit
      | stop == start =
        exit (emptyDeviceArray @a)
    rangeCreator !ets !start !stop !step !exit =
      if (stop > start && step <= 0) || (stop < start && step >= 0)
        then throwEdh ets UsageError "range is not converging"
        else runEdhTx ets $
          edhContIO $ do
            let (q, r) = quotRem (stop - start) step
                !len = if r == 0 then abs q else 1 + abs q
            !p <- callocArray @a len
            !fp <- newForeignPtr finalizerFree p
            let fillRng :: Int -> Int -> IO ()
                fillRng !n !i =
                  if i >= len
                    then return ()
                    else do
                      pokeElemOff p i $ fromIntegral n
                      fillRng (n + step) (i + 1)
            fillRng start 0
            atomically $ exit $ DeviceArray len fp
    randomCreator !ets !len !lowerValue !upperValue !exit =
      fromEdh ets lowerValue $ \ !lower -> fromEdh ets upperValue $ \ !upper ->
        if lower == upper
          then throwEdh ets UsageError "random range is zero-width"
          else do
            let (!lower', !upper') =
                  if lower < upper then (lower, upper) else (upper, lower)
            runEdhTx ets $
              edhContIO $ do
                !p <- callocArray @a len
                !fp <- newForeignPtr finalizerFree p
                let fillRnd :: Int -> IO ()
                    fillRnd !i =
                      if i < 0
                        then return ()
                        else do
                          !rv <- randomRIO (lower', upper')
                          pokeElemOff p i rv
                          fillRnd $ i - 1
                fillRnd $ len - 1
                atomically $ exit $ DeviceArray len fp
    nonzeroCreator !ets (DeviceArray !mcap !mfp) !exit = runEdhTx ets $
      edhContIO $
        withForeignPtr (castForeignPtr mfp) $
          \(mp :: Ptr YesNo) -> do
            !rp <- callocArray @Int mcap
            !rfp <- newForeignPtr finalizerFree rp
            let go i ri
                  | i >= mcap =
                    atomically $ exit (DeviceArray mcap rfp, ri)
                go i ri = do
                  !mv <- peekElemOff mp i
                  if mv /= 0
                    then do
                      pokeElemOff rp ri $ fromIntegral i
                      go (i + 1) (ri + 1)
                    else go (i + 1) ri
            go 0 0
    nonzeroCreator _ _ _ = error "bug: not a device array"

hostDataNumbering ::
  forall a.
  (Eq a, Ord a, Num a, Random a, EdhXchg a, Typeable a) =>
  a ->
  NumDataType
hostDataNumbering !def'val =
  NumDataType rangeCreator randomCreator nonzeroCreator
  where
    rangeCreator _ !start !stop _ !exit
      | stop == start =
        exit (emptyHostArray @a)
    rangeCreator !ets !start !stop !step !exit =
      if (stop > start && step <= 0) || (stop < start && step >= 0)
        then throwEdh ets UsageError "range is not converging"
        else runEdhTx ets $
          edhContIO $ do
            let (q, r) = quotRem (stop - start) step
                !len = if r == 0 then abs q else 1 + abs q
            !ha <- MV.unsafeNew len
            let fillRng :: Int -> Int -> IO ()
                fillRng !n !i =
                  if i >= len
                    then return ()
                    else do
                      MV.unsafeWrite ha i (fromIntegral n :: a)
                      fillRng (n + step) (i + 1)
            fillRng start 0
            atomically $ exit $ HostArray len ha
    randomCreator !ets !len !lowerValue !upperValue !exit =
      fromEdh ets lowerValue $
        \(lower :: a) -> fromEdh ets upperValue $ \(upper :: a) ->
          if lower == upper
            then throwEdh ets UsageError "random range is zero-width"
            else do
              let (!lower', !upper') =
                    if lower < upper then (lower, upper) else (upper, lower)
              runEdhTx ets $
                edhContIO $ do
                  !ha <- MV.unsafeNew len
                  let fillRnd :: Int -> IO ()
                      fillRnd !i =
                        if i < 0
                          then return ()
                          else do
                            !rv <- randomRIO (lower', upper')
                            MV.unsafeWrite ha i rv
                            fillRnd $ i - 1
                  fillRnd $ len - 1
                  atomically $ exit $ HostArray len ha
    nonzeroCreator !ets (DeviceArray !mcap !mfp) !exit = runEdhTx ets $
      edhContIO $
        withForeignPtr (castForeignPtr mfp) $
          \(mp :: Ptr YesNo) -> do
            !ha <- MV.unsafeNew mcap
            let go i ri | i >= mcap = do
                  MV.set (MV.unsafeSlice ri (mcap - ri) ha) def'val
                  atomically $ exit (HostArray mcap ha, ri)
                go i ri = do
                  !mv <- peekElemOff mp i
                  if mv /= 0
                    then do
                      MV.unsafeWrite ha ri (fromIntegral i :: a)
                      go (i + 1) (ri + 1)
                    else go (i + 1) ri
            go 0 0
    nonzeroCreator _ _ _ = error "bug: not a host array"

edhDataNumbering :: NumDataType
edhDataNumbering = NumDataType rangeCreator randomCreator nonzeroCreator
  where
    rangeCreator _ !start !stop _ !exit
      | stop == start = exit (emptyHostArray @EdhValue)
    rangeCreator !ets !start !stop !step !exit =
      if (stop > start && step <= 0) || (stop < start && step >= 0)
        then throwEdh ets UsageError "range is not converging"
        else runEdhTx ets $
          edhContIO $ do
            let (q, r) = quotRem (stop - start) step
                !len = if r == 0 then abs q else 1 + abs q
            !ha <- MV.unsafeNew len
            let fillRng :: Int -> Int -> IO ()
                fillRng !n !i =
                  if i >= len
                    then return ()
                    else do
                      MV.unsafeWrite ha i $
                        EdhDecimal (fromIntegral n :: Decimal)
                      fillRng (n + step) (i + 1)
            fillRng start 0
            atomically $ exit $ HostArray len ha
    randomCreator !ets !len !lowerValue !upperValue !exit =
      -- assuming not too many bits are needed with Edh decimal arrays
      -- device arrays can always be used to workaround the lack of random bits
      fromEdh ets lowerValue $ \(lower :: Float) ->
        fromEdh ets upperValue $ \(upper :: Float) ->
          if lower == upper
            then throwEdh ets UsageError "random range is zero-width"
            else do
              let (!lower', !upper') =
                    if lower < upper then (lower, upper) else (upper, lower)
              runEdhTx ets $
                edhContIO $ do
                  !ha <- MV.unsafeNew len
                  let fillRnd :: Int -> IO ()
                      fillRnd !i =
                        if i < 0
                          then return ()
                          else do
                            !rv <- randomRIO (lower', upper')
                            MV.unsafeWrite ha i $
                              EdhDecimal $ fromRational $ toRational rv
                            fillRnd $ i - 1
                  fillRnd $ len - 1
                  atomically $ exit $ HostArray len ha
    nonzeroCreator !ets (DeviceArray !mcap !mfp) !exit = runEdhTx ets $
      edhContIO $
        withForeignPtr (castForeignPtr mfp) $
          \(mp :: Ptr YesNo) -> do
            !ha <- MV.unsafeNew mcap
            let go i ri | i >= mcap = do
                  MV.set (MV.unsafeSlice ri (mcap - ri) ha) edhNA
                  atomically $ exit (HostArray mcap ha, ri)
                go i ri = do
                  !mv <- peekElemOff mp i
                  if mv /= 0
                    then do
                      MV.unsafeWrite ha ri $
                        EdhDecimal (fromIntegral i :: Decimal)
                      go (i + 1) (ri + 1)
                    else go (i + 1) ri
            go 0 0
    nonzeroCreator _ _ _ = error "bug: not a host array"
