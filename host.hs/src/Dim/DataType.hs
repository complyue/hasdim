-- | Numpy dtype inspired abstraction for vectorizable types of data
--
-- The data type system is extensible through the effect system of Edh
module Dim.DataType where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Monad
import qualified Data.ByteString.Internal as B
import Data.Dynamic
import Data.Maybe
import Data.Typeable hiding (TypeRep, typeOf, typeRep)
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Storable.Mutable as MVS
import Dim.XCHG
import Foreign as F
import Foreign.ForeignPtr.Unsafe
import Language.Edh.EHI
import System.Random
import Type.Reflection
import Prelude

-- * DataType holding runtime representation

type DataTypeIdent = AttrName

-- | Native types stored in shared memory with computing devices (GPU or CPU
-- with heavy SIMD orientation)
data DeviceDataType = DeviceDataType
  { device'data'type'ident :: !DataTypeIdent,
    device'data'type'holder ::
      forall r.
      (forall a. (Eq a, Storable a, EdhXchg a, Typeable a) => TypeRep a -> r) ->
      r,
    device'data'type'as'of'num ::
      forall r.
      r ->
      ( forall a.
        (Num a, Storable a, EdhXchg a, Typeable a) =>
        TypeRep a ->
        r
      ) ->
      r,
    device'data'type'as'of'float ::
      forall r.
      r ->
      ( forall a.
        (Floating a, Storable a, EdhXchg a, Typeable a) =>
        TypeRep a ->
        r
      ) ->
      r,
    device'data'type'as'of'random ::
      forall r.
      r ->
      ( forall a.
        (Random a, Eq a, Ord a, Storable a, EdhXchg a, Typeable a) =>
        TypeRep a ->
        r
      ) ->
      r
  }

instance Eq DeviceDataType where
  (DeviceDataType x'dti x'trh _ _ _) == (DeviceDataType y'dti y'trh _ _ _) =
    x'trh $ \x'tr -> y'trh $ \y'tr ->
      case x'tr `eqTypeRep` y'tr of
        Just HRefl | x'dti == y'dti -> True
        _ -> False

{- HLINT ignore "Use const" -}

mkFloatDataType ::
  forall a.
  (RealFloat a, Random a, Num a, Storable a, EdhXchg a, Typeable a) =>
  DataTypeIdent ->
  DeviceDataType
mkFloatDataType !dti =
  DeviceDataType
    dti
    ($ typeRep @a)
    (\_naExit exit -> exit (typeRep @a))
    (\_naExit exit -> exit (typeRep @a))
    (\_naExit exit -> exit (typeRep @a))

mkIntDataType ::
  forall a.
  (Integral a, Random a, Num a, Storable a, EdhXchg a, Typeable a) =>
  DataTypeIdent ->
  DeviceDataType
mkIntDataType !dti =
  DeviceDataType
    dti
    ($ typeRep @a)
    (\_naExit exit -> exit (typeRep @a))
    (\naExit _exit -> naExit)
    (\_naExit exit -> exit (typeRep @a))

-- | Lifted Haskell types as operated directly by the host language
data DirectDataType = DirectDataType
  { direct'data'type'ident :: !DataTypeIdent,
    direct'data'defv'holder ::
      forall r.
      (forall a. (Eq a, EdhXchg a, Typeable a) => a -> r) ->
      r,
    direct'data'type'as'of'num ::
      forall r.
      r ->
      ( forall a.
        (Num a, Eq a, EdhXchg a, Typeable a) =>
        TypeRep a ->
        r
      ) ->
      r,
    direct'data'type'as'of'random ::
      forall r.
      r ->
      ( forall a.
        (Random a, Eq a, Ord a, EdhXchg a, Typeable a) =>
        TypeRep a ->
        r
      ) ->
      r
  }

instance Eq DirectDataType where
  (DirectDataType x'dti x'dvh _ _) == (DirectDataType y'dti y'dvh _ _) =
    x'dvh $ \x'defv -> y'dvh $ \y'defv ->
      case typeOf x'defv `eqTypeRep` typeOf y'defv of
        Just HRefl | x'dti == y'dti && x'defv == y'defv -> True
        _ -> False

mkBoxDataType ::
  forall a.
  (Eq a, EdhXchg a, Typeable a) =>
  DataTypeIdent ->
  a ->
  DirectDataType
mkBoxDataType !dti !defv =
  DirectDataType
    dti
    ($ defv)
    (\naExit _exit -> naExit)
    (\naExit _exit -> naExit)

mkRealFracDataType ::
  forall a.
  (RealFrac a, Random a, Eq a, EdhXchg a, Typeable a) =>
  DataTypeIdent ->
  a ->
  DirectDataType
mkRealFracDataType !dti !defv =
  DirectDataType
    dti
    ($ defv)
    (\_naExit exit -> exit (typeRep @a))
    (\_naExit exit -> exit (typeRep @a))

withDeviceDataType ::
  forall r.
  Object ->
  r ->
  (forall a. (Eq a, Storable a, EdhXchg a, Typeable a) => TypeRep a -> r) ->
  r
withDeviceDataType !dto !naExit !exit = case edh'obj'store dto of
  HostStore (Dynamic trDataType monoDataType) ->
    case trDataType `eqTypeRep` typeRep @DeviceDataType of
      Just HRefl -> device'data'type'holder monoDataType exit
      _ -> naExit
  _ -> naExit

withDirectDataType ::
  forall r.
  Object ->
  r ->
  (forall a. (Eq a, EdhXchg a, Typeable a) => a -> r) ->
  r
withDirectDataType !dto !naExit !exit = case edh'obj'store dto of
  HostStore (Dynamic trDataType monoDataType) ->
    case trDataType `eqTypeRep` typeRep @DirectDataType of
      Just HRefl -> direct'data'defv'holder monoDataType exit
      _ -> naExit
  _ -> naExit

withDataType ::
  forall r. Object -> r -> (DeviceDataType -> r) -> (DirectDataType -> r) -> r
withDataType !dto !naExit !devExit !dirExit = case edh'obj'store dto of
  HostStore (Dynamic trDataType monoDataType) ->
    case trDataType `eqTypeRep` typeRep @DeviceDataType of
      Just HRefl -> devExit monoDataType
      _ -> case trDataType `eqTypeRep` typeRep @DirectDataType of
        Just HRefl -> dirExit monoDataType
        _ -> naExit
  _ -> naExit

dtypeEqProc :: EdhValue -> EdhHostProc
dtypeEqProc !other !exit !ets = case edhUltimate other of
  EdhObject !objOther ->
    withDataType objOther exitNeg withDeviceOther withDirectOther
  _ -> exitNeg
  where
    this = edh'scope'this $ contextScope $ edh'context ets

    withDeviceOther :: DeviceDataType -> STM ()
    withDeviceOther dtOther =
      withDataType
        this
        badThis
        ( \ !dtThis ->
            exitEdh ets exit $
              EdhBool $ dtThis == dtOther
        )
        (const exitNeg)

    withDirectOther :: DirectDataType -> STM ()
    withDirectOther dtOther = withDataType this badThis (const exitNeg) $
      \ !dtThis ->
        exitEdh ets exit $
          EdhBool $ dtThis == dtOther

    badThis = throwEdh ets EvalError "bug: not a host value of DataType"
    exitNeg = exitEdh ets exit $ EdhBool False

-- * Flat Array

type ArrayCapacity = Int

type ArrayLength = Int

type ArrayIndex = Int

class FlatArray f a where
  -- | allocated capacity, i.e. maximum number of valid elements
  array'capacity :: f a -> ArrayCapacity

  -- | duplicate to a new array of specified capacity, with specified number of
  -- valid elements copied
  array'duplicate :: f a -> ArrayLength -> ArrayCapacity -> IO (f a)

  -- | indexed reader
  array'reader :: f a -> (ArrayIndex -> IO a)

  -- | indexed writer
  array'writer :: f a -> (ArrayIndex -> a -> IO ())

  -- | convert to blob if possible
  array'as'blob :: forall r. f a -> ArrayLength -> r -> (B.ByteString -> r) -> r

data DeviceArray a = (EdhXchg a, Typeable a, Storable a) =>
  DeviceArray
  { device'array'cap :: !Int,
    device'array'ref :: !(ForeignPtr a)
  }

instance FlatArray DeviceArray a where
  array'capacity = deviceArrayCapacity
  array'duplicate = dupDeviceArray
  array'reader (DeviceArray _cap fp) = \ !i -> peekElemOff p i
    where
      -- note: withForeignPtr can not be safer here
      p = unsafeForeignPtrToPtr fp
  array'writer (DeviceArray _cap fp) = \ !i !a -> pokeElemOff p i a
    where
      -- note: withForeignPtr can not be safer here
      p = unsafeForeignPtrToPtr fp
  array'as'blob (DeviceArray _cap fp) !len _naExit !exit =
    exit $
      B.fromForeignPtr (castForeignPtr fp) 0 (len * sizeOf (undefined :: a))

data DirectArray a
  = (EdhXchg a, Typeable a) => DirectArray !(MV.IOVector a)

instance FlatArray DirectArray a where
  array'capacity = directArrayCapacity
  array'duplicate = dupDirectArray
  array'reader (DirectArray iov) = \ !i -> MV.unsafeRead iov i
  array'writer (DirectArray iov) = \ !i !a -> MV.unsafeWrite iov i a
  array'as'blob _a _len naExit _exit = naExit

emptyDeviceArray ::
  forall a. (EdhXchg a, Typeable a, Storable a) => IO (DeviceArray a)
emptyDeviceArray = do
  !np <- newForeignPtr_ nullPtr
  return $ DeviceArray @a 0 np

emptyDirectArray :: forall a. (EdhXchg a, Typeable a) => IO (DirectArray a)
emptyDirectArray = do
  !iov <- MV.new 0
  return $ DirectArray @a iov

newDeviceArray ::
  forall a.
  (Storable a, Eq a, EdhXchg a, Typeable a) =>
  ArrayCapacity ->
  IO (ForeignPtr a, DeviceArray a)
newDeviceArray !cap = do
  !p <- callocArray @a cap
  !fp <- newForeignPtr finalizerFree p
  return (fp, DeviceArray @a cap fp)

newDirectArray ::
  forall a.
  (Eq a, EdhXchg a, Typeable a) =>
  a ->
  ArrayCapacity ->
  IO (MV.IOVector a, DirectArray a)
newDirectArray !fill'val !cap = do
  !iov <- MV.unsafeNew cap
  MV.set iov fill'val
  return (iov, DirectArray @a iov)

dupDeviceArray ::
  DeviceArray a -> ArrayLength -> ArrayCapacity -> IO (DeviceArray a)
dupDeviceArray (DeviceArray !capSrc !fpSrc) !lenSrc !capNew = do
  !p' <- callocArray capNew
  !fp' <- newForeignPtr finalizerFree p'
  withForeignPtr fpSrc $
    \ !p -> copyArray p' p $ min capNew (min lenSrc capSrc)
  return $ DeviceArray capNew fp'

dupDirectArray ::
  DirectArray a -> ArrayLength -> ArrayCapacity -> IO (DirectArray a)
dupDirectArray (DirectArray !iovSrc) !lenSrc !capNew = do
  !iov' <- MV.new capNew
  let !cpLen = min lenSrc capNew
  when (cpLen > 0) $
    let !tgt = MV.unsafeSlice 0 cpLen iov'
        !src = MV.unsafeSlice 0 cpLen iovSrc
     in MV.copy tgt src
  return $ DirectArray iov'

deviceArrayCapacity :: DeviceArray a -> ArrayCapacity
deviceArrayCapacity (DeviceArray !cap _) = cap

directArrayCapacity :: DirectArray a -> ArrayCapacity
directArrayCapacity (DirectArray !vec) = MV.length vec

unsafeSliceDeviceArray ::
  DeviceArray a -> Int -> Int -> DeviceArray a
unsafeSliceDeviceArray (DeviceArray _ (fp :: ForeignPtr a)) !offset !len =
  DeviceArray @a len $
    plusForeignPtr fp $ sizeOf (undefined :: a) * offset

unsafeSliceDirectArray ::
  DirectArray a -> Int -> Int -> DirectArray a
unsafeSliceDirectArray (DirectArray !iov) !offset !len =
  let !iov' = MV.slice offset len iov in DirectArray iov'

unsafeDeviceArrayAsVector ::
  forall a. (Storable a) => DeviceArray a -> VS.Vector a
unsafeDeviceArrayAsVector (DeviceArray !cap !fp) =
  VS.unsafeFromForeignPtr0 (castForeignPtr fp) cap

unsafeDeviceArrayFromVector ::
  forall a.
  (EdhXchg a, Typeable a, Storable a) =>
  VS.Vector a ->
  DeviceArray a
unsafeDeviceArrayFromVector !vec = case VS.unsafeToForeignPtr0 vec of
  (!fp, !cap) -> DeviceArray @a cap (castForeignPtr fp)

unsafeDeviceArrayAsMVector ::
  forall a.
  (Storable a, EdhXchg a, Typeable a) =>
  DeviceArray a ->
  MVS.IOVector a
unsafeDeviceArrayAsMVector (DeviceArray !cap !fp) =
  MVS.unsafeFromForeignPtr0 (castForeignPtr fp) cap

unsafeDeviceArrayFromMVector ::
  forall a.
  (Storable a, EdhXchg a, Typeable a) =>
  MVS.IOVector a ->
  DeviceArray a
unsafeDeviceArrayFromMVector !mvec = case MVS.unsafeToForeignPtr0 mvec of
  (!fp, !cap) -> DeviceArray @a cap (castForeignPtr fp)
