-- | Contiguous 1-dimensional array interface
--
-- Subject to be re-interpreted as n-dimensional arrays per different indexing
-- schemas
module Dim.FlatArray where

-- import           Debug.Trace

import Control.Monad
import Control.Monad.IO.Class
import Data.Dynamic
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Storable.Mutable as MVS
import Event.Analytics.EHI
import Foreign
import Foreign.ForeignPtr.Unsafe
import Prelude

-- * Unified Flat Array Interface

-- todo SIMD optimizations?

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

  -- | obtain pointer to the underlying data if applicable
  array'data'ptr ::
    forall m r.
    (MonadPlus m) =>
    f a ->
    (Storable a => ForeignPtr a -> m r) ->
    m r

data DeviceArray a = (Storable a, EdhXchg a, Typeable a) =>
  DeviceArray
  { device'array'cap :: !Int,
    device'array'ref :: !(ForeignPtr a)
  }

instance FlatArray DeviceArray a where
  array'capacity = deviceArrayCapacity
  array'duplicate = dupDeviceArray
  array'reader (DeviceArray _cap fp) = \ !i -> liftIO $ peekElemOff p i
    where
      -- note: withForeignPtr can not be safer here
      p = unsafeForeignPtrToPtr fp
  array'writer (DeviceArray _cap fp) = \ !i !a -> liftIO $ pokeElemOff p i a
    where
      -- note: withForeignPtr can not be safer here
      p = unsafeForeignPtrToPtr fp
  array'data'ptr (DeviceArray _cap fp) = ($ fp)

data DirectArray a
  = (Eq a, EdhXchg a, Typeable a) => DirectArray !(MV.IOVector a)

instance FlatArray DirectArray a where
  array'capacity = directArrayCapacity
  array'duplicate = dupDirectArray
  array'reader (DirectArray iov) = \ !i -> liftIO $ MV.unsafeRead iov i
  array'writer (DirectArray iov) = \ !i !a -> liftIO $ MV.unsafeWrite iov i a
  array'data'ptr _a _ = mzero

emptyDeviceArray ::
  forall a. (EdhXchg a, Typeable a, Storable a) => IO (DeviceArray a)
emptyDeviceArray = liftIO $ do
  !np <- newForeignPtr_ nullPtr
  return $ DeviceArray @a 0 np

emptyDirectArray ::
  forall a. (Eq a, EdhXchg a, Typeable a) => IO (DirectArray a)
emptyDirectArray = liftIO $ do
  !iov <- MV.new 0
  return $ DirectArray @a iov

newDeviceArray ::
  forall a.
  (Eq a, Storable a, EdhXchg a, Typeable a) =>
  ArrayCapacity ->
  IO (ForeignPtr a, DeviceArray a)
newDeviceArray !cap = liftIO $ do
  !p <- callocArray @a cap
  !fp <- newForeignPtr finalizerFree p
  return (fp, DeviceArray @a cap fp)

newDirectArray ::
  forall a.
  (Eq a, EdhXchg a, Typeable a) =>
  ArrayCapacity ->
  IO (MV.IOVector a, DirectArray a)
newDirectArray = newDirectArray' $ edhDefaultValue @a

newDirectArray' ::
  forall a.
  (Eq a, EdhXchg a, Typeable a) =>
  a ->
  ArrayCapacity ->
  IO (MV.IOVector a, DirectArray a)
newDirectArray' !fill'val !cap = liftIO $ do
  !iov <- MV.unsafeNew cap
  MV.set iov fill'val
  return (iov, DirectArray @a iov)

dupDeviceArray ::
  DeviceArray a -> ArrayLength -> ArrayCapacity -> IO (DeviceArray a)
dupDeviceArray (DeviceArray !capSrc !fpSrc) !lenSrc !capNew = liftIO $ do
  !p' <- callocArray capNew
  !fp' <- newForeignPtr finalizerFree p'
  withForeignPtr fpSrc $
    \ !p -> copyArray p' p $ min capNew (min lenSrc capSrc)
  return $ DeviceArray capNew fp'

dupDirectArray ::
  DirectArray a -> ArrayLength -> ArrayCapacity -> IO (DirectArray a)
dupDirectArray (DirectArray !iovSrc) !lenSrc !capNew = liftIO $ do
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
