module Dim.DbArray where

-- import           Debug.Trace

{-

import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import qualified Data.ByteString as B
import qualified Data.ByteString.Internal as B
import Data.Dynamic
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE
import qualified Data.Lossless.Decimal as D
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Storable.Mutable as MVS
import Dim.DataType
import Dim.XCHG
import Foreign hiding (void)
import Foreign.ForeignPtr.Unsafe (unsafeForeignPtrToPtr)
import Language.Edh.EHI
import System.Directory (createDirectoryIfMissing)
import System.FilePath (takeDirectory, (</>))
import System.IO (IOMode (ReadWriteMode), hFileSize, withFile)
import System.IO.MMap (Mode (ReadWriteEx), mmapFileForeignPtr)
import Type.Reflection
import Prelude

-- | The shape of an array is named dimensions with size of each
-- zero-dimension shape is prohibited here (by NonEmpty list as container)
-- zero-sized dimensions are prohibited by parseArrayShape
newtype ArrayShape = ArrayShape (NonEmpty (DimName, DimSize)) deriving (Eq)

instance Show ArrayShape where
  show (ArrayShape shape) =
    concat $
      ["("]
        ++ ( ( \(n, s) ->
                 (if n == "" then show s else T.unpack n <> " := " <> show s) <> ", "
             )
               <$> NE.toList shape
           )
        ++ [")"]

type DimName = Text

type DimSize = Int

dbArraySize1d :: ArrayShape -> DimSize
dbArraySize1d (ArrayShape !shape) = snd $ NE.head shape

dbArraySize :: ArrayShape -> DimSize
dbArraySize (ArrayShape !shape) = product (snd <$> shape)

flatIndexInShape ::
  EdhThreadState -> [EdhValue] -> ArrayShape -> (DimSize -> STM ()) -> STM ()
flatIndexInShape !ets !idxs (ArrayShape !shape) !exit =
  if length idxs /= NE.length shape
    then
      throwEdh ets UsageError $
        "dim of index mismatch shape: "
          <> T.pack (show $ length idxs)
          <> " vs "
          <> T.pack (show $ NE.length shape)
    else flatIdx (reverse idxs) (reverse $ NE.toList shape) exit
  where
    flatIdx :: [EdhValue] -> [(DimName, DimSize)] -> (DimSize -> STM ()) -> STM ()
    flatIdx [] [] !exit' = exit' 0
    flatIdx (EdhDecimal d : restIdxs) ((_, ds) : restDims) !exit' =
      case D.decimalToInteger d of
        Just d' ->
          let s' = case fromIntegral d' of
                s | s < 0 -> s + ds -- numpy style negative indexing
                s -> s
           in if s' < 0 || s' >= ds
                then
                  throwEdh ets UsageError $
                    "index out of bounds: "
                      <> T.pack (show d')
                      <> " vs "
                      <> T.pack (show ds)
                else flatIdx restIdxs restDims $ \i -> exit' $ ds * i + s'
        Nothing ->
          throwEdh ets UsageError $ "index not an integer: " <> T.pack (show d)
    flatIdx _ _ _ = throwEdh ets UsageError "invalid index"

parseArrayShape ::
  EdhThreadState -> EdhValue -> (ArrayShape -> STM ()) -> STM ()
parseArrayShape !ets !val !exit = case val of
  EdhArgsPack (ArgsPack [!dim1] _) ->
    parseDim dim1 $ \ !pd -> exit $ ArrayShape $ pd :| []
  EdhArgsPack (ArgsPack (dim1 : dims) _) -> parseDim dim1 $ \ !pd ->
    seqcontSTM (parseDim <$> dims) $ \ !pds -> exit $ ArrayShape $ pd :| pds
  !dim1 -> parseDim dim1 $ \ !pd -> exit $ ArrayShape $ pd :| []
  where
    parseDim :: EdhValue -> ((DimName, DimSize) -> STM ()) -> STM ()
    parseDim v@(EdhDecimal d) !exit' = case D.decimalToInteger d of
      Just size | size > 0 -> exit' ("", fromInteger size)
      _ -> edhValueRepr ets v $
        \r -> throwEdh ets UsageError $ "invalid dimension size: " <> r
    parseDim v@(EdhNamedValue name (EdhDecimal d)) !exit' =
      case D.decimalToInteger d of
        Just size | size > 0 -> exit' (name, fromInteger size)
        _ -> edhValueRepr ets v $
          \r -> throwEdh ets UsageError $ "invalid dimension size: " <> r
    parseDim v _ = edhValueRepr ets v $
      \r -> throwEdh ets UsageError $ "invalid dimension spec: " <> r

edhArrayShape :: ArrayShape -> EdhValue
edhArrayShape (ArrayShape !shape) =
  EdhArgsPack $
    ArgsPack (edhDim <$> NE.toList shape) odEmpty
  where
    edhDim :: (DimName, DimSize) -> EdhValue
    edhDim ("", size) = EdhDecimal $ fromIntegral size
    edhDim (name, size) = EdhNamedValue name $ EdhDecimal $ fromIntegral size

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

-- | Disk backed array
data DbArray where
  DbArray ::
    { -- | root dir for data files
      db'array'dir :: !Text,
      -- | data file path relative to root
      db'array'path :: !Text,
      -- | dtype
      -- | flat storage, armed after current tx in an IO action
      db'array'dtype :: !DataType,
      db'array'store :: !(TMVar (Either SomeException (ArrayShape, Ptr DbArrayHeader, FlatArray)))
    } ->
    DbArray

mmapDbArray ::
  TMVar (Either SomeException (ArrayShape, Ptr DbArrayHeader, FlatArray)) ->
  Text ->
  Text ->
  DataType ->
  Maybe ArrayShape ->
  IO ()
mmapDbArray !asVar !dataDir !dataPath !dt !maybeShape =
  case data'type'proxy dt of
    HostDataType {} -> error "bug: host dtype passed to mmapDbArray"
    DeviceDataType (_ :: TypeRep a) !item'size !item'align ->
      case maybeShape of
        -- create if not exists, or load existing file with truncation
        Just !shape ->
          handle (atomically . void . tryPutTMVar asVar . Left) $ do
            let !cap = dbArraySize shape
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
                                + cap
                                * item'size
                        when
                          ( fromIntegral (dbArraySize1d shape)
                              < array'data'length hdr
                          )
                          $ throwIO $
                            userError $
                              "len1d of shape "
                                <> show (dbArraySize1d shape)
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
                                  fromIntegral $ array'data'offset hdr
                        atomically $ do
                          void $ tryTakeTMVar asVar
                          void $
                            tryPutTMVar asVar $
                              Right
                                (shape, hdrLongLive, fa)

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
                  atomically $ do
                    void $ tryTakeTMVar asVar
                    void $
                      tryPutTMVar asVar $
                        Right
                          ( shape,
                            hdrLongLive,
                            DeviceArray @a cap $
                              plusForeignPtr fp $
                                fromIntegral $ array'data'offset hdr
                          )

        -- load existing array file, use header and file length to calculate
        -- shape, assuming 1d
        Nothing ->
          handle (atomically . void . tryPutTMVar asVar . Left) $
            withFile dataFilePath ReadWriteMode $
              \ !dfh ->
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
                    atomically $ do
                      void $ tryTakeTMVar asVar
                      void $
                        tryPutTMVar asVar $
                          Right
                            ( ArrayShape (("", cap) :| []),
                              hdrLongLive,
                              DeviceArray @a cap $
                                plusForeignPtr fp $
                                  fromIntegral $ array'data'offset hdr
                            )

                  -- don't have a header long enough, most prolly not existing
                  -- todo more care of abnormal situations
                  _ ->
                    throwIO $
                      userError $
                        "invalid disk file for array: "
                          <> dataFilePath
  where
    !dataFilePath = T.unpack dataDir </> T.unpack (dataPath <> ".dba")
    !dataFileDir = takeDirectory dataFilePath

-- | unwrap an array from Edh object form
unwrapDbArrayObject :: Object -> STM (Maybe DbArray)
unwrapDbArrayObject = (fmap snd <$>) . castObjectStore

dbArrayShape :: DbArray -> STM ArrayShape
dbArrayShape (DbArray _ _ _ !das) =
  readTMVar das >>= \case
    Left !err -> throwSTM err
    Right (!shape, _, _) -> return shape

castDbArrayData ::
  forall a.
  (Storable a, EdhXchg a, Typeable a) =>
  DbArray ->
  IO (VS.Vector a)
castDbArrayData (DbArray _ _ _ !das) =
  atomically (readTMVar das) >>= \case
    Left !err -> throwIO err
    Right (_, !hdrPtr, !fa) -> do
      !vlen <- readDbArrayLength hdrPtr
      return $
        unsafeFlatArrayAsVector $
          unsafeSliceFlatArray fa 0 $
            fromIntegral
              vlen

castMutDbArrayData ::
  forall a.
  (Storable a, EdhXchg a, Typeable a) =>
  DbArray ->
  IO (MVS.IOVector a)
castMutDbArrayData (DbArray _ _ _ !das) =
  atomically (readTMVar das) >>= \case
    Left !err -> throwIO err
    Right (_, !hdrPtr, !fa) -> do
      !vlen <- readDbArrayLength hdrPtr
      return $
        unsafeFlatArrayAsMVector $
          unsafeSliceFlatArray fa 0 $
            fromIntegral
              vlen

castFullDbArrayData ::
  forall a.
  (Storable a, EdhXchg a, Typeable a) =>
  DbArray ->
  IO (VS.Vector a)
castFullDbArrayData (DbArray _ _ _ !das) =
  atomically (readTMVar das) >>= \case
    Left !err -> throwIO err
    Right (_, _, !fa) -> return $ unsafeFlatArrayAsVector fa

castMutFullDbArrayData ::
  forall a.
  (Storable a, EdhXchg a, Typeable a) =>
  DbArray ->
  IO (MVS.IOVector a)
castMutFullDbArrayData (DbArray _ _ _ !das) =
  atomically (readTMVar das) >>= \case
    Left !err -> throwIO err
    Right (_, _, !fa) -> return $ unsafeFlatArrayAsMVector fa

-}
