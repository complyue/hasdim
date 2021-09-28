module Dim.DbArray where

-- import           Debug.Trace

import Control.Applicative
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
import Dim.FlatArray
import Event.Analytics.EHI
import Foreign hiding (void)
import Foreign.ForeignPtr.Unsafe (unsafeForeignPtrToPtr)
import Language.Edh.MHI
import System.Directory
import System.FilePath
import System.IO
import System.IO.MMap
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
  [EdhValue] -> ArrayShape -> Edh DimSize
flatIndexInShape !idxs (ArrayShape !shape) =
  if length idxs /= NE.length shape
    then
      throwEdhM UsageError $
        "dim of index mismatch shape: "
          <> T.pack (show $ length idxs)
          <> " vs "
          <> T.pack (show $ NE.length shape)
    else flatIdx (reverse idxs) (reverse $ NE.toList shape)
  where
    flatIdx :: [EdhValue] -> [(DimName, DimSize)] -> Edh DimSize
    flatIdx [] [] = return 0
    flatIdx (EdhDecimal d : restIdxs) ((_, ds) : restDims) =
      case D.decimalToInteger d of
        Just d' ->
          let s' = case fromIntegral d' of
                s | s < 0 -> s + ds -- numpy style negative indexing
                s -> s
           in if s' < 0 || s' >= ds
                then
                  throwEdhM UsageError $
                    "index out of bounds: "
                      <> T.pack (show d')
                      <> " vs "
                      <> T.pack (show ds)
                else flatIdx restIdxs restDims >>= \i -> return $ ds * i + s'
        Nothing ->
          throwEdhM UsageError $ "index not an integer: " <> T.pack (show d)
    flatIdx _ _ = throwEdhM UsageError "invalid index"

parseArrayShape :: EdhValue -> Edh ArrayShape
parseArrayShape !val = case val of
  EdhArgsPack (ArgsPack [!dim1] _) ->
    parseDim dim1 >>= \ !pd -> return $ ArrayShape $ pd :| []
  EdhArgsPack (ArgsPack (dim1 : dims) _) -> do
    !pd <- parseDim dim1
    !pds <- sequence (parseDim <$> dims)
    return $ ArrayShape $ pd :| pds
  !dim1 -> parseDim dim1 >>= \ !pd -> return $ ArrayShape $ pd :| []
  where
    parseDim :: EdhValue -> Edh (DimName, DimSize)
    parseDim v@(EdhDecimal d) = case D.decimalToInteger d of
      Just size | size > 0 -> return ("", fromInteger size)
      _ ->
        edhValueReprM v
          >>= \r -> throwEdhM UsageError $ "invalid dimension size: " <> r
    parseDim v@(EdhNamedValue name (EdhDecimal d)) =
      case D.decimalToInteger d of
        Just size | size > 0 -> return (name, fromInteger size)
        _ ->
          edhValueReprM v
            >>= \r -> throwEdhM UsageError $ "invalid dimension size: " <> r
    parseDim v =
      edhValueReprM v
        >>= \r -> throwEdhM UsageError $ "invalid dimension spec: " <> r

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
data DbArray a = (Eq a, Storable a, EdhXchg a, Typeable a) =>
  DbArray
  { -- | root dir for data files
    db'array'dir :: !Text,
    -- | data file path relative to root
    db'array'path :: !Text,
    -- | flat storage, armed after current tx in an IO action
    db'array'store ::
      !( TMVar
           (Either SomeException (ArrayShape, Ptr DbArrayHeader, DeviceArray a))
       )
  }

mmapDbArray ::
  forall a.
  (Eq a, Storable a, EdhXchg a, Typeable a) =>
  TMVar (Either SomeException (ArrayShape, Ptr DbArrayHeader, DeviceArray a)) ->
  Text ->
  Text ->
  Maybe ArrayShape ->
  Bool ->
  IO ()
mmapDbArray !asVar !dataDir !dataPath !maybeShape !overwrite = do
  when overwrite $
    catch (removeFile dataFilePath) $ \(_ :: IOException) -> pure ()
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
                      $ throwHostIO UsageError $
                        T.pack $
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
                throwHostIO UsageError $
                  "invalid disk file for array: " <> T.pack dataFilePath
  where
    !dataFilePath = T.unpack dataDir </> T.unpack (dataPath <> ".dba")
    !dataFileDir = takeDirectory dataFilePath
    item'size = sizeOf (undefined :: a)
    item'align = alignment (undefined :: a)

dbArrayShape :: forall a. DbArray a -> STM ArrayShape
dbArrayShape !dba =
  readTMVar (db'array'store dba) >>= \case
    Left !err -> throwSTM err
    Right (!shape, _, _) -> return shape

asDbArrayOf ::
  forall a m r.
  (MonadPlus m, Typeable a) =>
  Object ->
  (DbArray a -> m r) ->
  m r
asDbArrayOf !obj !exit = case dynamicHostData obj of
  Nothing -> mzero
  Just (Dynamic trDBA dba) ->
    case trDBA `eqTypeRep` typeRep @(DbArray a) of
      Nothing -> mzero
      Just HRefl -> exit dba

asDbArrayOf' ::
  forall a m r.
  (MonadPlus m, Typeable a) =>
  EdhValue ->
  (DbArray a -> m r) ->
  m r
asDbArrayOf' !val !exit = case edhUltimate val of
  EdhObject !obj -> asDbArrayOf obj exit
  _ -> mzero

withDbArrayOf :: forall a. Typeable a => Object -> Edh (Object, DbArray a)
withDbArrayOf !obj = do
  supers <- readTVarEdh $ edh'obj'supers obj
  withComposition $ obj : supers
  where
    withComposition :: [Object] -> Edh (Object, DbArray a)
    withComposition [] = naM ""
    withComposition (o : rest) =
      asDbArrayOf @a o (return . (o,)) <|> withComposition rest

withDbArrayOf' :: forall a. Typeable a => EdhValue -> Edh (Object, DbArray a)
withDbArrayOf' !val = case edhUltimate val of
  EdhObject !obj -> do
    withDbArrayOf obj
  _ -> naM ""

withDbArraySelfOf :: forall a. Typeable a => Edh (Object, DbArray a)
withDbArraySelfOf = do
  that <- edh'scope'that . contextScope . edh'context <$> edhThreadState
  (withDbArrayOf @a that <|>) $
    throwEdhM UsageError $
      "not an expected self DbArray of type " <> T.pack (show $ typeRep @a)

withDbArraySelf ::
  forall r.
  ( forall a.
    (Eq a, Storable a, EdhXchg a, Typeable a) =>
    Object ->
    DbArray a ->
    Edh r
  ) ->
  Edh r
withDbArraySelf !dbaExit = do
  that <- edh'scope'that . contextScope . edh'context <$> edhThreadState
  supers <- readTVarEdh $ edh'obj'supers that
  withComposition $ that : supers
  where
    withComposition :: [Object] -> Edh r
    withComposition [] = naM "not an expected self DbArray"
    withComposition (o : rest) = case dynamicHostData o of
      Nothing -> withComposition rest
      Just (Dynamic trDBA dba) -> case trDBA of
        App trDBAC _trA -> case trDBAC `eqTypeRep` typeRep @DbArray of
          Nothing -> withComposition rest
          Just HRefl -> case dba of -- need this case to witness its instances
            dba'@DbArray {} -> dbaExit o dba'
        _ -> withComposition rest

getDbArrayDtype :: Object -> Edh Object
getDbArrayDtype !objAry = readTVarEdh (edh'obj'supers objAry) >>= findColDto
  where
    findColDto :: [Object] -> Edh Object
    findColDto [] = do
      badDesc <- edhSimpleDescM (EdhObject objAry)
      naM $ "not a DbArray with dtype: " <> badDesc
    -- this is right and avoids unnecessary checks in vastly usual cases
    findColDto [dto] = return dto
    -- safe guard in case a DbArray instance has been further extended
    findColDto (maybeDto : rest) =
      withDataType maybeDto (const $ return maybeDto) <|> findColDto rest
