{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Numpy dtype inspired abstraction for vectorizable types of data
--
-- The data type system is extensible through the effect system of Edh
module Dim.DataType where

import           Prelude
-- import           Debug.Trace

import           System.IO.Unsafe               ( unsafePerformIO )
import           GHC.Conc                       ( unsafeIOToSTM )

import           Foreign                       as F

import           Control.Monad.Reader

import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.Dynamic
import           Data.Proxy

import qualified Data.Vector.Mutable           as MV
import qualified Data.Vector.Storable          as VS
import qualified Data.Vector.Storable.Mutable  as MVS

import           Language.Edh.EHI

import           Dim.XCHG


data FlatArray where
  DeviceArray ::(EdhXchg a, Storable a) => {
      device'array'cap :: !Int
    , device'array'ref :: !(ForeignPtr a)
    } -> FlatArray
  HostArray ::(EdhXchg a) => {
      host'array'cap :: !Int
    , host'array'ref :: !(MV.IOVector a)
    } -> FlatArray


emptyDeviceArray :: forall a . (EdhXchg a, Storable a) => FlatArray
emptyDeviceArray = unsafePerformIO $ do
  !np <- newForeignPtr_ nullPtr
  return $ DeviceArray @a 0 np
{-# NOINLINE emptyDeviceArray #-}

emptyHostArray :: forall a . (EdhXchg a) => FlatArray
emptyHostArray = unsafePerformIO $ do
  !ha <- MV.new 0
  return $ HostArray @a 0 ha
{-# NOINLINE emptyHostArray #-}


newDeviceArray :: forall a . (EdhXchg a, Storable a) => Int -> IO FlatArray
newDeviceArray !cap = do
  !p  <- callocArray @a cap
  !fp <- newForeignPtr finalizerFree p
  return $ DeviceArray @a cap fp

newHostArray :: forall a . (EdhXchg a) => Int -> IO FlatArray
newHostArray !cap = do
  !ha <- MV.new cap
  return $ HostArray @a cap ha


dupFlatArray :: FlatArray -> Int -> Int -> IO FlatArray
dupFlatArray (DeviceArray !capSrc !fpSrc) !lenSrc !capNew = do
  !p'  <- callocArray capNew
  !fp' <- newForeignPtr finalizerFree p'
  withForeignPtr fpSrc $ \ !p -> copyArray p' p $ min capNew (min lenSrc capSrc)
  return $ DeviceArray capNew fp'
dupFlatArray (HostArray _capSrc !haSrc) !lenSrc !capNew = do
  !ha' <- MV.new capNew
  let !cpLen = min lenSrc capNew
  when (cpLen > 0)
    $ let !tgt = MV.unsafeSlice 0 cpLen ha'
          !src = MV.unsafeSlice 0 cpLen haSrc
      in  MV.copy tgt src
  return $ HostArray capNew ha'


flatArrayCapacity :: FlatArray -> Int
flatArrayCapacity (DeviceArray !cap _) = cap
flatArrayCapacity (HostArray   !cap _) = cap


flatArrayNumBytes :: FlatArray -> Int
flatArrayNumBytes (DeviceArray !cap (_fp :: ForeignPtr a)) =
  cap * sizeOf (undefined :: a)
flatArrayNumBytes (HostArray !cap _) = cap * 8


unsafeSliceFlatArray :: FlatArray -> Int -> Int -> FlatArray
unsafeSliceFlatArray (DeviceArray _ (fp :: ForeignPtr a)) !offset !len =
  DeviceArray @a len $ plusForeignPtr fp $ offset * sizeOf (undefined :: a)
unsafeSliceFlatArray (HostArray _ !ha) !offset !len =
  let !ha' = MV.slice offset len ha in HostArray len ha'


unsafeFlatArrayAsVector :: forall a . (Storable a) => FlatArray -> VS.Vector a
unsafeFlatArrayAsVector (DeviceArray !cap fp) =
  VS.unsafeFromForeignPtr0 (castForeignPtr fp) cap

unsafeFlatArrayFromVector
  :: forall a . (EdhXchg a, Storable a) => VS.Vector a -> FlatArray
unsafeFlatArrayFromVector !vec = case VS.unsafeToForeignPtr0 vec of
  (!fp, !cap) -> DeviceArray @a cap (castForeignPtr fp)

unsafeFlatArrayAsMVector
  :: forall a . (Storable a, EdhXchg a) => FlatArray -> MVS.IOVector a
unsafeFlatArrayAsMVector (DeviceArray !cap !fp) =
  MVS.unsafeFromForeignPtr0 (castForeignPtr fp) cap

unsafeFlatArrayFromMVector
  :: forall a . (Storable a, EdhXchg a) => MVS.IOVector a -> FlatArray
unsafeFlatArrayFromMVector !mvec = case MVS.unsafeToForeignPtr0 mvec of
  (!fp, !cap) -> DeviceArray @a cap (castForeignPtr fp)


type DataTypeIdent = Text

data DataTypeProxy where
  DeviceDataType ::(EdhXchg a, Storable a) => {
      device'data'type ::Proxy a
    , device'data'size :: !Int
    , device'data'align :: !Int
    } -> DataTypeProxy
  HostDataType ::(EdhXchg a ) => Proxy a -> DataTypeProxy

-- | DataType facilitates the basic support of a data type to be managable
-- by HasDim, i.e. array allocation, element read/write, array bulk update.
--
-- More sophisticated, vectorized operations are supported by other collections
-- of routines, as they tends to have more demanding premises than required
-- here.
data DataType where
  DataType ::{
      data'type'identifier :: !DataTypeIdent
    , data'type'proxy :: !DataTypeProxy
    , flat'new'array :: Int -> STM FlatArray
    , flat'grow'array :: FlatArray  -> Int -> STM FlatArray
    , flat'array'read :: EdhThreadState -> FlatArray
        -> Int -> (EdhValue -> STM ()) -> STM ()
    , flat'array'write :: EdhThreadState -> FlatArray
        -> Int -> EdhValue -> (EdhValue -> STM ()) -> STM ()
    , flat'array'update :: EdhThreadState
        -> [(Int, EdhValue)]  -> FlatArray   -> STM () -> STM ()
    } -> DataType
instance Eq DataType where
  x == y = data'type'identifier x == data'type'identifier y


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
    withThisHostObj ets $ \_hsv !dt ->
      withHostObject' dtoOther (exitEdh ets exit $ EdhBool False)
        $ \_hsv !dtOther ->
            exitEdh ets exit
              $  EdhBool
              $  data'type'identifier dtOther
              == data'type'identifier dt
  dtypeEqProc _ !exit !ets = exitEdh ets exit $ EdhBool False

  dtypeIdentProc :: EdhHostProc
  dtypeIdentProc _ !exit !ets = withThisHostObj ets
    $ \_hsv !dt -> exitEdh ets exit $ EdhString $ data'type'identifier dt


makeDeviceDataType
  :: forall a
   . (EdhXchg a, Storable a, Typeable a)
  => DataTypeIdent
  -> DataType
makeDeviceDataType !dti = DataType
  dti
  (DeviceDataType (Proxy :: Proxy a)
                  (sizeOf (undefined :: a))
                  (alignment (undefined :: a))
  )
  createArray
  growArray
  readArrayCell
  writeArrayCell
  updateArray
 where
  createArray !cap = unsafeIOToSTM (newDeviceArray @a cap)
  growArray (DeviceArray !cap !fp) !newCap = unsafeIOToSTM $ do
    !p'  <- callocArray newCap
    !fp' <- newForeignPtr finalizerFree p'
    withForeignPtr fp $ \ !p -> copyArray p' p $ min newCap cap
    return $ DeviceArray newCap fp'
  readArrayCell !ets (DeviceArray !cap !fp) !idx !exit =
    edhRegulateIndex ets cap idx $ \ !posIdx -> do
      sv <- unsafeIOToSTM $ withForeignPtr fp $ \ !vPtr ->
        peekElemOff vPtr posIdx
      toEdh ets sv $ \ !val -> exit val
  writeArrayCell !ets (DeviceArray !cap !fp) !idx !val !exit =
    edhRegulateIndex ets cap idx $ \ !posIdx -> fromEdh ets val $ \ !sv -> do
      unsafeIOToSTM $ withForeignPtr fp $ \ !vPtr -> pokeElemOff vPtr posIdx sv
      toEdh ets sv $ \ !val' -> exit val'
  updateArray _ [] _ !exit = exit
  updateArray !ets ((!idx, !val) : rest'upds) ary@(DeviceArray !cap !fp) !exit
    = edhRegulateIndex ets cap idx $ \ !posIdx ->
      fromEdh @a ets val $ \ !sv -> do
        unsafeIOToSTM $ withForeignPtr (castForeignPtr fp) $ \ !vPtr ->
          pokeElemOff vPtr posIdx sv
        updateArray ets rest'upds ary exit


-- makeHostDataType
--   :: forall a . (EdhXchg a, Typeable a) => DataTypeIdent -> DataType
-- makeHostDataType !dti = DataType dti 
--                                  (sizeOf (undefined :: a))
--                                  (alignment (undefined :: a))
--                                  createArray
--                                  growArray
--                                  readArrayCell
--                                  writeArrayCell
--                                  updateArray
--  where
--   createArray !cap = unsafeIOToSTM (newHostArray cap)
--   growArray (HostArray !cap !fp) !newCap = unsafeIOToSTM $ do
--     !p'  <- callocArray newCap
--     !fp' <- newForeignPtr finalizerFree p'
--     withForeignPtr fp $ \ !p -> copyArray p' p $ min newCap cap
--     return $ HostArray newCap fp'
--   readArrayCell !ets (HostArray !cap !fp) !idx !exit =
--     edhRegulateIndex ets cap idx $ \ !posIdx -> do
--       sv <- unsafeIOToSTM $ withForeignPtr fp $ \ !vPtr ->
--         peekElemOff vPtr posIdx
--       toEdh ets sv $ \ !val -> exit val
--   writeArrayCell !ets (HostArray !cap !fp) !idx !val !exit =
--     edhRegulateIndex ets cap idx $ \ !posIdx -> fromEdh ets val $ \ !sv -> do
--       unsafeIOToSTM $ withForeignPtr fp $ \ !vPtr -> pokeElemOff vPtr posIdx sv
--       toEdh ets sv $ \ !val' -> exit val'
--   updateArray _ [] _ !exit = exit
--   updateArray !ets ((!idx, !sv) : rest'upds) ary@(HostArray !cap !fp) !exit =
--     edhRegulateIndex ets cap idx $ \ !posIdx -> do
--       unsafeIOToSTM $ withForeignPtr fp $ \ !vPtr -> pokeElemOff vPtr posIdx sv
--       updateArray ets rest'upds ary exit


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


data FlatOrd where
  FlatOrd ::{
      flat'cmp'vectorized :: EdhThreadState -> FlatArray
        -> (Ordering -> Bool) -> EdhValue -> (FlatArray -> STM ()) -> STM ()
    , flat'cmp'element'wise :: EdhThreadState -> FlatArray
        -> (Ordering -> Bool) -> FlatArray  -> (FlatArray -> STM ()) -> STM ()
  }-> FlatOrd
 deriving Typeable
flatOrd :: forall a . (Ord a, Storable a, Typeable a, EdhXchg a) => FlatOrd
flatOrd = FlatOrd vecCmp elemCmp
 where
  -- vectorized comparation, yielding a new YesNo array
  vecCmp !ets (DeviceArray !cap !fp) !cmp !v !exit =
    fromEdh @a ets v $ \ !sv ->
      (exit =<<) $ unsafeIOToSTM $ withForeignPtr (castForeignPtr fp) $ \ !p ->
        do
          !rp  <- callocArray @YesNo cap
          !rfp <- newForeignPtr finalizerFree rp
          let go i | i >= cap = return $ DeviceArray cap rfp
              go i            = do
                ev <- peekElemOff p i
                pokeElemOff rp i $ if cmp $ compare @a ev sv then 1 else 0
                go (i + 1)
          go 0
  -- element-wise comparation, yielding a new YesNo array
  elemCmp _ets (DeviceArray !cap1 !fp1) !cmp (DeviceArray _cap2 !fp2) !exit =
    (exit =<<)
      $ unsafeIOToSTM
      $ withForeignPtr (castForeignPtr fp1)
      $ \(p1 :: Ptr a) ->
          withForeignPtr (castForeignPtr fp2) $ \(p2 :: Ptr a) -> do
            !rp  <- callocArray @YesNo cap1
            !rfp <- newForeignPtr finalizerFree rp
            let go i | i >= cap1 = return $ DeviceArray cap1 rfp
                go i             = do
                  ev1 <- peekElemOff p1 i
                  ev2 <- peekElemOff p2 i
                  pokeElemOff rp i $ if cmp $ compare ev1 ev2 then 1 else 0
                  go (i + 1)
            go 0

resolveDataComparator
  :: forall a
   . (Typeable FlatOrd)
  => EdhThreadState
  -> DataTypeIdent
  -> FlatArray
  -> (FlatOrd -> STM ())
  -> STM ()
resolveDataComparator !ets !dti !fa =
  resolveDataComparator' ets dti fa
    $  throwEdh ets UsageError
    $  "ordering not supported by dtype: "
    <> dti
resolveDataComparator'
  :: forall a
   . (Typeable FlatOrd)
  => EdhThreadState
  -> DataTypeIdent
  -> FlatArray
  -> STM ()
  -> (FlatOrd -> STM ())
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
    "float64" -> exitWith $ toDyn (flatOrd @Double)
    "float32" -> exitWith $ toDyn (flatOrd @Float)
    "int64"   -> exitWith $ toDyn (flatOrd @Int64)
    "int32"   -> exitWith $ toDyn (flatOrd @Int32)
    "int8"    -> exitWith $ toDyn (flatOrd @Int8)
    "byte"    -> exitWith $ toDyn (flatOrd @Int8)
    "intp"    -> exitWith $ toDyn (flatOrd @Int)
    "yesno"   -> exitWith $ toDyn (flatOrd @YesNo)
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


data FlatOp where
  FlatOp ::{
      flat'extract'yesno :: EdhThreadState -> FlatArray -> FlatArray
        -> ((FlatArray , Int) -> STM ()) -> STM ()
    , flat'extract'fancy :: EdhThreadState -> FlatArray -> FlatArray
        -> (FlatArray  -> STM ()) -> STM ()

    , flat'op'vectorized :: EdhThreadState -> FlatArray
        -> Dynamic -> EdhValue -> (FlatArray  -> STM ()) -> STM ()
    , flat'op'element'wise :: EdhThreadState -> FlatArray
        -> Dynamic -> FlatArray  -> (FlatArray  -> STM ()) -> STM ()

    , flat'inp'vectorized :: EdhThreadState -> FlatArray
        -> Dynamic -> EdhValue -> STM () -> STM ()
    , flat'inp'vectorized'slice :: EdhThreadState -> (Int,Int,Int) -> FlatArray
        -> Dynamic -> EdhValue -> STM () -> STM ()
    , flat'inp'vectorized'masked :: EdhThreadState -> FlatArray -> FlatArray
        -> Dynamic -> EdhValue -> STM () -> STM ()
    , flat'inp'vectorized'fancy :: EdhThreadState -> FlatArray -> FlatArray
        -> Dynamic -> EdhValue -> STM () -> STM ()

    , flat'inp'element'wise :: EdhThreadState -> FlatArray
        -> Dynamic -> FlatArray  -> STM () -> STM ()
    , flat'inp'element'wise'slice :: EdhThreadState -> (Int,Int,Int) -> FlatArray
        -> Dynamic -> FlatArray  -> STM () -> STM ()
    , flat'inp'element'wise'masked :: EdhThreadState -> FlatArray -> FlatArray
        -> Dynamic -> FlatArray  -> STM () -> STM ()
    , flat'inp'element'wise'fancy :: EdhThreadState -> FlatArray -> FlatArray
        -> Dynamic -> FlatArray  -> STM () -> STM ()
  }-> FlatOp
 deriving Typeable
flatOp :: forall a . (EdhXchg a, Storable a, Typeable a) => FlatOp
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
  vecExtractBool _ets (DeviceArray !mcap !mfp) (DeviceArray _cap !fp) !exit =
    (exit =<<)
      $ unsafeIOToSTM
      $ withForeignPtr (castForeignPtr mfp)
      $ \(mp :: Ptr YesNo) ->
          withForeignPtr (castForeignPtr fp) $ \(p :: Ptr a) -> do
            !rp  <- callocArray mcap
            !rfp <- newForeignPtr finalizerFree rp
            let go i ri | i >= mcap = return (DeviceArray mcap rfp, ri)
                go i ri             = do
                  mv <- peekElemOff mp i
                  if mv /= 0
                    then do
                      peekElemOff p i >>= pokeElemOff rp ri
                      go (i + 1) (ri + 1)
                    else go (i + 1) ri
            go 0 0
  -- vectorized data extraction with a fancy index, yielding a new array
  vecExtractFancy !ets (DeviceArray !icap !ifp) (DeviceArray !cap !fp) !exit =
    do
      !result <- unsafeIOToSTM $ withForeignPtr fp $ \ !p ->
        withForeignPtr (castForeignPtr ifp) $ \(ip :: Ptr Int) -> do
          !rp  <- callocArray icap
          !rfp <- newForeignPtr finalizerFree rp
          let go i | i >= icap = return $ Right $ DeviceArray icap rfp
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
  vecOp !ets (DeviceArray !cap !fp) !dop !v !exit = case fromDynamic dop of
    Nothing                  -> error "bug: dtype op type mismatch"
    Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv ->
      (exit =<<)
        $ unsafeIOToSTM
        $ withForeignPtr (castForeignPtr fp)
        $ \(p :: Ptr a) -> do
            !rp  <- callocArray cap
            !rfp <- newForeignPtr finalizerFree rp
            let go i | i >= cap = return $ DeviceArray cap rfp
                go i            = do
                  ev <- peekElemOff p i
                  pokeElemOff rp i $ op ev sv
                  go (i + 1)
            go 0
  -- element-wise operation, yielding a new array
  elemOp _ets (DeviceArray !cap1 !fp1) !dop (DeviceArray _cap2 !fp2) !exit =
    case fromDynamic dop of
      Nothing -> error "bug: dtype op type mismatch"
      Just (op :: a -> a -> a) ->
        (exit =<<)
          $ unsafeIOToSTM
          $ withForeignPtr (castForeignPtr fp1)
          $ \(p1 :: Ptr a) ->
              withForeignPtr (castForeignPtr fp2) $ \(p2 :: Ptr a) -> do
                !rp  <- callocArray cap1
                !rfp <- newForeignPtr finalizerFree rp
                let go i | i >= cap1 = return $ DeviceArray cap1 rfp
                    go i             = do
                      ev1 <- peekElemOff p1 i
                      ev2 <- peekElemOff p2 i
                      pokeElemOff rp i $ op ev1 ev2
                      go (i + 1)
                go 0
  -- vectorized operation, inplace modifying the array
  vecInp !ets (DeviceArray !cap !fp) !dop !v !exit = case fromDynamic dop of
    Nothing                  -> error "bug: dtype op type mismatch"
    Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv ->
      (>> exit)
        $ unsafeIOToSTM
        $ withForeignPtr (castForeignPtr fp)
        $ \(p :: Ptr a) -> do
            let go i | i >= cap = return ()
                go i            = do
                  ev <- peekElemOff p i
                  pokeElemOff p i $ op ev sv
                  go (i + 1)
            go 0
  -- vectorized operation, inplace modifying the array, with a slice spec
  vecInpSlice !ets (!start, !stop, !step) (DeviceArray _cap !fp) !dop !v !exit
    = case fromDynamic dop of
      Nothing                  -> error "bug: dtype op type mismatch"
      Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv ->
        (>> exit)
          $ unsafeIOToSTM
          $ withForeignPtr (castForeignPtr fp)
          $ \(p :: Ptr a) -> do
              let (q, r) = quotRem (stop - start) step
                  !len   = if r == 0 then abs q else 1 + abs q
              let go _ i | i >= len = return ()
                  go n i            = do
                    ev <- peekElemOff p n
                    pokeElemOff p n $ op ev sv
                    go (n + step) (i + 1)
              go start 0
  -- vectorized operation, inplace modifying the array, with a yesno mask
  vecInpMasked !ets (DeviceArray _cap !mfp) (DeviceArray !cap !fp) !dop !v !exit
    = case fromDynamic dop of
      Nothing                  -> error "bug: dtype op type mismatch"
      Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv ->
        (>> exit)
          $ unsafeIOToSTM
          $ withForeignPtr (castForeignPtr mfp)
          $ \(mp :: Ptr YesNo) ->
              withForeignPtr (castForeignPtr fp) $ \(p :: Ptr a) -> do
                let go i | i >= cap = return ()
                    go i            = do
                      mv <- peekElemOff mp i
                      when (mv /= 0) $ do
                        ev <- peekElemOff p i
                        pokeElemOff p i $ op ev sv
                      go (i + 1)
                go 0
  -- vectorized operation, inplace modifying the array, with a fancy index
  vecInpFancy !ets (DeviceArray !icap !ifp) (DeviceArray !cap !fp) !dop !v !exit
    = case fromDynamic dop of
      Nothing                  -> error "bug: dtype op type mismatch"
      Just (op :: a -> a -> a) -> fromEdh ets v $ \ !sv -> do
        !badIdx <-
          unsafeIOToSTM
          $ withForeignPtr (castForeignPtr ifp)
          $ \(ip :: Ptr Int) ->
              withForeignPtr (castForeignPtr fp) $ \(p :: Ptr a) -> do
                let go i | i >= icap = return 0
                    go i             = peekElemOff ip i >>= \ !idx ->
                      if idx < 0 || idx >= cap
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
  elemInp _ets (DeviceArray !cap1 !fp1) !dop (DeviceArray _cap2 !fp2) !exit =
    case fromDynamic dop of
      Nothing -> error "bug: dtype op type mismatch"
      Just (op :: a -> a -> a) ->
        (>> exit)
          $ unsafeIOToSTM
          $ withForeignPtr (castForeignPtr fp1)
          $ \(p1 :: Ptr a) ->
              withForeignPtr (castForeignPtr fp2) $ \(p2 :: Ptr a) -> do
                let go i | i >= cap1 = return ()
                    go i             = do
                      ev1 <- peekElemOff p1 i
                      ev2 <- peekElemOff p2 i
                      pokeElemOff p1 i $ op ev1 ev2
                      go (i + 1)
                go 0
  -- element-wise operation, inplace modifying array, with a slice spec
  elemInpSlice _ets (!start, !stop, !step) (DeviceArray _cap1 !fp1) !dop (DeviceArray !cap2 !fp2) !exit
    = case fromDynamic dop of
      Nothing -> error "bug: dtype op type mismatch"
      Just (op :: a -> a -> a) ->
        (>> exit)
          $ unsafeIOToSTM
          $ withForeignPtr (castForeignPtr fp1)
          $ \(p1 :: Ptr a) ->
              withForeignPtr (castForeignPtr fp2) $ \(p2 :: Ptr a) -> do
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
  elemInpMasked _ets (DeviceArray _cap !mfp) (DeviceArray !cap1 !fp1) !dop (DeviceArray _cap2 !fp2) !exit
    = case fromDynamic dop of
      Nothing -> error "bug: dtype op type mismatch"
      Just (op :: a -> a -> a) ->
        (>> exit)
          $ unsafeIOToSTM
          $ withForeignPtr (castForeignPtr mfp)
          $ \(mp :: Ptr YesNo) ->
              withForeignPtr (castForeignPtr fp1) $ \(p1 :: Ptr a) ->
                withForeignPtr (castForeignPtr fp2) $ \(p2 :: Ptr a) -> do
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
  elemInpFancy !ets (DeviceArray !icap !ifp) (DeviceArray !cap1 !fp1) !dop (DeviceArray !cap2 !fp2) !exit
    = case fromDynamic dop of
      Nothing                  -> error "bug: dtype op type mismatch"
      Just (op :: a -> a -> a) -> do
        !badIdx <-
          unsafeIOToSTM
          $ withForeignPtr (castForeignPtr ifp)
          $ \(ip :: Ptr Int) ->
              withForeignPtr (castForeignPtr fp1) $ \(p1 :: Ptr a) ->
                withForeignPtr (castForeignPtr fp2) $ \(p2 :: Ptr a) -> do
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
  :: EdhThreadState
  -> DataTypeIdent
  -> FlatArray
  -> (FlatOp -> STM ())
  -> STM ()
resolveDataOperator !ets !dti !fa =
  resolveDataOperator' ets dti fa
    $  throwEdh ets UsageError
    $  "operation not supported by dtype: "
    <> dti
resolveDataOperator'
  :: EdhThreadState
  -> DataTypeIdent
  -> FlatArray
  -> STM ()
  -> (FlatOp -> STM ())
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
    "float64" -> exitWith $ toDyn (flatOp @Double)
    "float32" -> exitWith $ toDyn (flatOp @Float)
    "int64"   -> exitWith $ toDyn (flatOp @Int64)
    "int32"   -> exitWith $ toDyn (flatOp @Int32)
    "int8"    -> exitWith $ toDyn (flatOp @Int8)
    "byte"    -> exitWith $ toDyn (flatOp @Int8)
    "intp"    -> exitWith $ toDyn (flatOp @Int)
    "yesno"   -> exitWith $ toDyn (flatOp @YesNo)
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
        -> Int -> Int -> Int -> (FlatArray  -> STM ()) -> STM ()
    , flat'new'nonzero'array :: EdhThreadState
        -> FlatArray -> ((FlatArray , Int) -> STM ()) -> STM ()
    }-> FlatRanger a
 deriving Typeable
flatRanger
  :: forall a . (Num a, EdhXchg a, Storable a, Typeable a) => FlatRanger a
flatRanger = FlatRanger rangeCreator nonzeroCreator
 where
  rangeCreator _ !start !stop _ !exit | stop == start =
    exit (emptyDeviceArray @a)
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
        return $ DeviceArray len fp
  nonzeroCreator _ (DeviceArray !mcap !mfp) !exit =
    (exit =<<)
      $ unsafeIOToSTM
      $ withForeignPtr (castForeignPtr mfp)
      $ \(mp :: Ptr YesNo) -> do
          !rp  <- callocArray @YesNo mcap
          !rfp <- newForeignPtr finalizerFree rp
          let go i ri | i >= mcap = return (DeviceArray mcap rfp, ri)
              go i ri             = do
                mv <- peekElemOff mp i
                if mv /= 0
                  then do
                    pokeElemOff rp ri $ fromIntegral i
                    go (i + 1) (ri + 1)
                  else go (i + 1) ri
          go 0 0
