-- | Contiguous 1-dimensional array interface
--
-- Subject to be re-interpreted as n-dimensional arrays per different indexing
-- schemas
module Dim.FlatArray where

-- import           Debug.Trace

import Control.Applicative
import Control.Exception
import Control.Monad
import Control.Monad.IO.Class
import qualified Data.ByteString as B
import qualified Data.ByteString.Internal as B
import Data.Dynamic
import qualified Data.Text as T
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Storable.Mutable as MVS
import Event.Analytics.EHI
import Foreign
import Foreign.ForeignPtr.Unsafe
import Language.Edh.EHI
import System.Directory
import System.FilePath
import System.IO
import System.IO.MMap
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
    ((Storable a) => ForeignPtr a -> m r) ->
    m r

data DeviceArray a
  = (Storable a, EdhXchg a, Typeable a) =>
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
    plusForeignPtr fp $
      sizeOf (undefined :: a) * offset

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

data DbArrayHeader = DbArrayHeader
  { -- | version of file data layout
    array'layout'version :: {-# UNPACK #-} !Int32,
    -- | a.k.a. padded header size
    array'data'offset :: {-# UNPACK #-} !Int32,
    -- | padded item size
    array'item'size :: {-# UNPACK #-} !Int32,
    -- | alignment required for an item
    array'item'align :: {-# UNPACK #-} !Int32,
    -- | number of valid items in the array, to be read/written on-the-fly
    -- rest of the file content should be considered pre-allocated capacity
    array'data'length :: {-# UNPACK #-} !Int64
  }
  deriving (Eq)

instance Storable DbArrayHeader where
  -- this is highly fragile in covering different ISA or even C compilers or
  -- even different versions of them, which is used to build the Python/Numpy
  -- and other programs we interchange data files with.
  --
  -- strive to be compliant with mainstream toolchains of Ubuntu 18.04 on x64,
  -- as far as working with decent macOS on x64 during development.
  peek !ptr = do
    !ver <- peekByteOff ptr 0
    !doff <- peekByteOff ptr 4
    !isz <- peekByteOff ptr 8
    !ial <- peekByteOff ptr 12
    !vlen <- peekByteOff ptr 16
    return $ DbArrayHeader ver doff isz ial vlen
  poke !ptr (DbArrayHeader !ver !doff !isz ial !vlen) = do
    pokeByteOff ptr 0 ver
    pokeByteOff ptr 4 doff
    pokeByteOff ptr 8 isz
    pokeByteOff ptr 12 ial
    pokeByteOff ptr 16 vlen

  -- a disk file for array is always mmaped from beginning, data following the
  -- header. align the header so start of data is aligned with at least 512
  -- bits for possible SIMD performance improvement or even compliance
  alignment _ = 64

  -- so 40 bytes is unused in the head as far
  sizeOf _ = 24

dbArrayHeaderSize, dbArrayHeaderAlign :: Int
dbArrayHeaderSize = sizeOf (undefined :: DbArrayHeader)
dbArrayHeaderAlign = alignment (undefined :: DbArrayHeader)

readDbArrayLength :: Ptr DbArrayHeader -> IO Int64
readDbArrayLength !ptr = peekByteOff ptr 16

writeDbArrayLength :: Ptr DbArrayHeader -> Int64 -> IO ()
writeDbArrayLength !ptr !vlen = pokeByteOff ptr 16 vlen

dbArrayHeaderV0 :: Int -> Int -> DbArrayHeader
dbArrayHeaderV0 !item'size !item'align =
  DbArrayHeader
    { array'layout'version = 0,
      array'data'offset =
        fromIntegral $
          dbArrayHeaderAlign
            * (1 + div dbArrayHeaderSize dbArrayHeaderAlign),
      array'item'size = fromIntegral item'size,
      array'item'align = fromIntegral item'align,
      array'data'length = 0
    }

mmapDBA ::
  forall a.
  (Eq a, Storable a, EdhXchg a, Typeable a) =>
  String ->
  Maybe Int ->
  Bool ->
  IO (Ptr DbArrayHeader, DeviceArray a)
mmapDBA !dataFilePath !maybeCap !overwrite = do
  when overwrite $
    catch (removeFile dataFilePath) $
      \(_ :: IOException) -> pure ()
  case maybeCap of
    -- create if not exists, or load existing file with truncation
    Just !cap -> do
      createDirectoryIfMissing True dataFileDir
      withFile dataFilePath ReadWriteMode $ \ !dfh ->
        B.hGetNonBlocking dfh dbArrayHeaderSize >>= \case
          -- existing and with a header long enough
          !headerPayload | B.length headerPayload == dbArrayHeaderSize ->
            do
              let (!fpHdr, !fpOffHdr, _) = B.toForeignPtr headerPayload
              withForeignPtr (plusForeignPtr fpHdr fpOffHdr) $
                \ !pHdr' -> do
                  let (pHdr :: Ptr DbArrayHeader) = castPtr pHdr'
                  !hdr <- peek pHdr
                  let !mmap'size =
                        fromIntegral (array'data'offset hdr)
                          + cap * item'size
                  when
                    (fromIntegral cap < array'data'length hdr)
                    $ throwHostIO UsageError
                    $ T.pack
                    $ "specified cap "
                      <> show cap
                      <> " too small to cover valid data in data file: "
                      <> show (array'data'length hdr)
                  -- mind to avoid truncating file shorter,
                  -- i.e. possible data loss
                  (fp, _, _) <-
                    mmapFileForeignPtr dataFilePath ReadWriteEx $
                      Just (0, mmap'size)
                  let !hdrLongLive =
                        unsafeForeignPtrToPtr $ castForeignPtr fp
                      !fa =
                        DeviceArray @a cap $
                          plusForeignPtr fp $
                            fromIntegral $
                              array'data'offset hdr
                  return (hdrLongLive, fa)

          -- don't have a header long enough, most prolly not existing
          -- todo more care for abnormal situations
          _ -> do
            let !hdr = dbArrayHeaderV0 item'size item'align
                !mmap'size =
                  fromIntegral (array'data'offset hdr) + cap * item'size
            (fp, _, _) <-
              mmapFileForeignPtr dataFilePath ReadWriteEx $
                Just (0, mmap'size)
            let !hdrLongLive = unsafeForeignPtrToPtr $ castForeignPtr fp
            poke hdrLongLive hdr
            return
              ( hdrLongLive,
                DeviceArray @a cap $
                  plusForeignPtr fp $
                    fromIntegral $
                      array'data'offset hdr
              )

    -- load existing array file, use header and file length to calculate
    -- shape, assuming 1d
    Nothing -> withFile dataFilePath ReadWriteMode $ \ !dfh ->
      hFileSize dfh >>= \case
        -- existing and with a header long enough
        !fileSize | fileSize >= fromIntegral dbArrayHeaderSize -> do
          (fp, _, _) <-
            mmapFileForeignPtr dataFilePath ReadWriteEx $
              Just (0, fromIntegral fileSize)
          let !hdrLongLive =
                unsafeForeignPtrToPtr $ castForeignPtr fp
          !hdr <- peek hdrLongLive
          let data'bytes'len :: Int64 =
                fromIntegral fileSize
                  - fromIntegral (array'data'offset hdr)
              cap :: Int =
                fromIntegral
                  data'bytes'len
                  `div` fromIntegral item'size
          return
            ( hdrLongLive,
              DeviceArray @a cap $
                plusForeignPtr fp $
                  fromIntegral $
                    array'data'offset hdr
            )

        -- don't have a header long enough, most prolly not existing
        -- todo more care of abnormal situations
        _ ->
          throwHostIO UsageError $
            "invalid disk file for array: " <> T.pack dataFilePath
  where
    !dataFileDir = takeDirectory dataFilePath
    item'size = sizeOf (undefined :: a)
    item'align = alignment (undefined :: a)
