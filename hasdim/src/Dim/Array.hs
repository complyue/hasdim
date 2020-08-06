{-# LANGUAGE AllowAmbiguousTypes #-}

module Dim.Array where

import           Prelude
-- import           Debug.Trace

import           Foreign.ForeignPtr.Unsafe
import           Foreign                 hiding ( void )
import qualified Data.ByteString               as B
import qualified Data.ByteString.Internal      as B

import           System.FilePath
import           System.Directory
import           System.IO
import           System.IO.MMap

import           Control.Monad
import           Control.Exception
import           Control.Concurrent.STM

import           Data.List.NonEmpty             ( NonEmpty(..) )
import qualified Data.List.NonEmpty            as NE

import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.HashMap.Strict           as Map
import           Data.Unique
import           Data.Coerce
import           Data.Dynamic

import           Data.Vector.Storable           ( Vector )

import qualified Data.Lossless.Decimal         as D
import           Language.Edh.EHI

import           Dim.XCHG
import           Dim.DataType


-- | The shape of an array is named dimensions with size of each
-- zero-dimension shape is prohibited here (by NonEmpty list as container)
-- zero-sized dimensions are prohibited by parseArrayShape
newtype ArrayShape = ArrayShape (NonEmpty (DimName, DimSize)) deriving (Eq)
instance Show ArrayShape where
  show (ArrayShape shape) =
    concat
      $  ["("]
      ++ (   (\(n, s) ->
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

flatIndexInShape
  :: EdhProgState -> [EdhValue] -> ArrayShape -> (DimSize -> STM ()) -> STM ()
flatIndexInShape !pgs !idxs (ArrayShape !shape) !exit =
  if length idxs /= NE.length shape
    then
      throwEdhSTM pgs UsageError
      $  "NDim of index mismatch shape: "
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
              s | s < 0 -> s + ds  -- numpy style negative indexing
              s         -> s
        in  if s' < 0 || s' >= ds
              then
                throwEdhSTM pgs UsageError
                $  "Index out of bounds: "
                <> T.pack (show d')
                <> " vs "
                <> T.pack (show ds)
              else flatIdx restIdxs restDims $ \i -> exit' $ ds * i + s'
      Nothing ->
        throwEdhSTM pgs UsageError $ "Index not an integer: " <> T.pack (show d)
  flatIdx _ _ _ = throwEdhSTM pgs UsageError "Invalid index"

parseArrayShape :: EdhProgState -> EdhValue -> (ArrayShape -> STM ()) -> STM ()
parseArrayShape !pgs !val !exit = case val of
  EdhArgsPack (ArgsPack [!dim1] _) ->
    parseDim dim1 $ \pd -> exit $ ArrayShape $ pd :| []
  EdhArgsPack (ArgsPack (dim1 : dims) _) -> parseDim dim1 $ \pd ->
    seqcontSTM (parseDim <$> dims) $ \pds -> exit $ ArrayShape $ pd :| pds
  !dim1 -> parseDim dim1 $ \pd -> exit $ ArrayShape $ pd :| []
 where
  parseDim :: EdhValue -> ((DimName, DimSize) -> STM ()) -> STM ()
  parseDim v@(EdhDecimal d) !exit' = case D.decimalToInteger d of
    Just size | size > 0 -> exit' ("", fromInteger size)
    _                    -> edhValueReprSTM pgs v
      $ \r -> throwEdhSTM pgs UsageError $ "Invalid dimension size: " <> r
  parseDim v@(EdhNamedValue name (EdhDecimal d)) !exit' =
    case D.decimalToInteger d of
      Just size | size > 0 -> exit' (name, fromInteger size)
      _                    -> edhValueReprSTM pgs v
        $ \r -> throwEdhSTM pgs UsageError $ "Invalid dimension size: " <> r
  parseDim v _ = edhValueReprSTM pgs v
    $ \r -> throwEdhSTM pgs UsageError $ "Invalid dimension spec: " <> r

edhArrayShape :: ArrayShape -> EdhValue
edhArrayShape (ArrayShape !shape) = EdhArgsPack
  $ ArgsPack (edhDim <$> NE.toList shape) odEmpty
 where
  edhDim :: (DimName, DimSize) -> EdhValue
  edhDim (""  , size) = EdhDecimal $ fromIntegral size
  edhDim (name, size) = EdhNamedValue name $ EdhDecimal $ fromIntegral size


data DbArrayHeader = DbArrayHeader {
    -- | version of file data layout
    array'layout'version :: {-# UNPACK #-} !Int32
    -- | a.k.a. padded header size
  , array'data'offset :: {-# UNPACK #-} !Int32
    -- | padded item size
  , array'item'size :: {-# UNPACK #-} !Int32
    -- | alignment required for an item
  , array'item'align :: {-# UNPACK #-} !Int32
    -- | number of valid items in the array, to be read/written on-the-fly
    -- rest of the file content should be considered pre-allocated capacity
  , array'data'length :: {-# UNPACK #-} !Int64
  } deriving (Eq)
instance Storable DbArrayHeader where
  -- this is highly fragile in covering different ISA or even C compilers or
  -- even different versions of them, which is used to build the Python/Numpy
  -- and other programs we interchange data files with.
  --
  -- strive to be compliant with mainstream toolchains of Ubuntu 18.04 on x64,
  -- as far as working with decent macOS on x64 during development.
  peek !ptr = do
    !ver  <- peekByteOff ptr 0
    !doff <- peekByteOff ptr 4
    !isz  <- peekByteOff ptr 8
    !ial  <- peekByteOff ptr 12
    !vlen <- peekByteOff ptr 16
    return $ DbArrayHeader ver doff isz ial vlen
  poke !ptr (DbArrayHeader !ver !doff !isz ial !vlen) = do
    pokeByteOff ptr 0  ver
    pokeByteOff ptr 4  doff
    pokeByteOff ptr 8  isz
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


dbArrayHeaderV0 :: forall a . (Storable a) => DbArrayHeader
dbArrayHeaderV0 = DbArrayHeader
  { array'layout'version = 0
  , array'data'offset    = fromIntegral
                           $ dbArrayHeaderAlign
                           * (1 + div dbArrayHeaderSize dbArrayHeaderAlign)
  , array'item'size      = fromIntegral $ sizeOf (undefined :: a)
  , array'item'align     = fromIntegral $ alignment (undefined :: a)
  , array'data'length    = 0
  }


-- | Disk backed array
data DbArray where
  DbArray ::(Storable a, EdhXchg a) => {
      db'array'dir   :: !Text  -- ^ root dir for data files
    , db'array'path  :: !Text  -- ^ data file path relative to root
    , db'array'dtype :: !DataType  -- ^ dtype
      -- | flat storage, armed after current tx in an IO action
    , db'array'store :: !(TMVar (Either SomeException (ArrayShape, Ptr DbArrayHeader, FlatArray a)))
    } -> DbArray

mmapDbArray
  :: TMVar (Either SomeException (ArrayShape, Ptr DbArrayHeader, FlatArray a))
  -> Text
  -> Text
  -> DataType
  -> Maybe ArrayShape
  -> IO ()
mmapDbArray !asVar !dataDir !dataPath (DataType _dti (dts :: FlatStorable a)) =
  \case

    -- create if not exists, or load existing file with truncation
    Just !shape -> handle (atomically . void . tryPutTMVar asVar . Left) $ do
      let !cap = dbArraySize shape
      createDirectoryIfMissing True dataFileDir
      withFile dataFilePath ReadWriteMode $ \ !dfh ->
        B.hGetNonBlocking dfh dbArrayHeaderSize >>= \case

          -- existing and with a header long enough
          !headerPayload | B.length headerPayload == dbArrayHeaderSize -> do
            let (!fpHdr, !fpOffHdr, _) = B.toForeignPtr headerPayload
            withForeignPtr (plusForeignPtr fpHdr fpOffHdr) $ \ !pHdr' -> do
              let (pHdr :: Ptr DbArrayHeader) = castPtr pHdr'
              !hdr <- peek pHdr
              let
                !mmap'size =
                  fromIntegral (array'data'offset hdr)
                    + cap
                    * flat'element'size dts
              when (fromIntegral (dbArraySize1d shape) < array'data'length hdr)
                $  throwIO
                $  userError
                $  "Len1d of shape "
                <> show (dbArraySize1d shape)
                <> " too small to cover valid data in data file: "
                <> show (array'data'length hdr)
              -- mind to avoid truncating file shorter, i.e. possible data loss
              (fp, _, _) <- mmapFileForeignPtr @a dataFilePath ReadWriteEx
                $ Just (0, mmap'size)
              let !hdrLongLive = unsafeForeignPtrToPtr $ castForeignPtr fp
              void $ atomically $ tryPutTMVar asVar $ Right
                ( shape
                , hdrLongLive
                , FlatArray cap
                $ coerce
                $ plusForeignPtr fp
                $ fromIntegral
                $ array'data'offset hdr
                )

          -- don't have a header long enough, most prolly not existing
          -- todo more care for abnormal situations
          _ -> do
            let
              !hdr = dbArrayHeaderV0 @a
              !mmap'size =
                fromIntegral (array'data'offset hdr)
                  + cap
                  * flat'element'size dts
            (fp, _, _) <- mmapFileForeignPtr @a dataFilePath ReadWriteEx
              $ Just (0, mmap'size)
            let !hdrLongLive = unsafeForeignPtrToPtr $ castForeignPtr fp
            poke hdrLongLive hdr
            void $ atomically $ tryPutTMVar asVar $ Right
              ( shape
              , hdrLongLive
              , FlatArray cap
              $ coerce
              $ plusForeignPtr fp
              $ fromIntegral
              $ array'data'offset hdr
              )

    -- load existing array file, use header and file length to calculate shape,
    -- assuming 1d
    Nothing ->
      handle (atomically . void . tryPutTMVar asVar . Left)
        $ withFile dataFilePath ReadWriteMode
        $ \ !dfh -> hFileSize dfh >>= \case

            -- existing and with a header long enough
            !fileSize | fileSize >= fromIntegral dbArrayHeaderSize -> do
              (fp, _, _) <- mmapFileForeignPtr @a dataFilePath ReadWriteEx
                $ Just (0, fromIntegral fileSize)
              let !hdrLongLive = unsafeForeignPtrToPtr $ castForeignPtr fp
              !hdr <- peek hdrLongLive
              let data'bytes'len :: Int64 =
                    fromIntegral fileSize - fromIntegral (array'data'offset hdr)
                  cap :: Int = fromIntegral data'bytes'len
                    `div` fromIntegral (flat'element'size dts)
              void $ atomically $ tryPutTMVar asVar $ Right
                ( ArrayShape (("", cap) :| [])
                , hdrLongLive
                , FlatArray cap
                $ coerce
                $ plusForeignPtr fp
                $ fromIntegral
                $ array'data'offset hdr
                )

            -- don't have a header long enough, most prolly not existing
            -- todo more care of abnormal situations
            _ ->
              throwIO
                $  userError
                $  "Invalid disk file for array: "
                <> dataFilePath

 where
  !dataFilePath = T.unpack dataDir </> T.unpack (dataPath <> ".dba")
  !dataFileDir  = takeDirectory dataFilePath


-- | unwrap an array from Edh object form
unwrapDbArrayObject :: Object -> STM (Maybe DbArray)
unwrapDbArrayObject = castObjectStore

castDbArrayData
  :: forall a . (Storable a, EdhXchg a) => DbArray -> IO (Vector a)
castDbArrayData (DbArray _ _ (DataType _dti (_dts :: FlatStorable a1)) !das) =
  atomically (readTMVar das) >>= \case
    Left  !err              -> throwIO err
    Right (_, !hdrPtr, !fa) -> do
      !vlen <- readDbArrayLength hdrPtr
      return
        $ unsafeFlatArrayAsVector
        $ unsafeSliceFlatArray fa 0
        $ fromIntegral vlen


-- | host constructor DbArray(dataDir, dataPath, dtype=float64, shape=None)
aryCtor :: EdhValue -> EdhHostCtor
aryCtor !defaultDt !pgsCtor !apk !ctorExit =
  case parseArgsPack ("", "", defaultDt, nil) ctorArgsParser apk of
    Left  err -> throwEdhSTM pgsCtor UsageError err
    Right (dataDir, dataPath, dtv, shapeVal) -> castObjectStore' dtv >>= \case
      Nothing -> throwEdhSTM pgsCtor UsageError "Invalid dtype"
      Just dt@(DataType _dti (_dts :: FlatStorable a)) ->
        if dataDir == "" || dataPath == ""
          then throwEdhSTM pgsCtor UsageError "Missing dataDir/dataPath"
          else if shapeVal == EdhNil
            then do
              asVar <- newEmptyTMVar
              edhContIO pgsCtor
                $ mmapDbArray @a asVar dataDir dataPath dt Nothing
              ctorExit $ toDyn $ DbArray @a dataDir dataPath dt asVar
            else parseArrayShape pgsCtor shapeVal $ \ !shape -> do
              asVar <- newEmptyTMVar
              edhContIO pgsCtor
                $ mmapDbArray @a asVar dataDir dataPath dt
                $ Just shape
              ctorExit $ toDyn $ DbArray @a dataDir dataPath dt asVar
 where
  ctorArgsParser =
    ArgsPackParser
        [ \arg (_, dataPath', dtv', shape') -> case arg of
          EdhString dataDir -> Right (dataDir, dataPath', dtv', shape')
          _                 -> Left "Invalid dataDir"
        , \arg (dataDir', _, dtv', shape') -> case arg of
          EdhString dataPath -> Right (dataDir', dataPath, dtv', shape')
          _                  -> Left "Invalid dataPath"
        , \arg (dataDir', dataPath', _, shape') -> case edhUltimate arg of
          dtv@EdhObject{} -> Right (dataDir', dataPath', dtv, shape')
          !badDtype ->
            Left $ "Bad dtype identifier of " <> T.pack (edhTypeNameOf badDtype)
        , \arg (dataDir', dataPath', dtype', _) ->
          Right (dataDir', dataPath', dtype', arg)
        ]
      $ Map.fromList
          [ ( "dtype"
            , \arg (dataDir', dataPath', _, shape') -> case edhUltimate arg of
              dtv@EdhObject{} -> Right (dataDir', dataPath', dtv, shape')
              !badDtype       -> Left $ "Bad dtype identifier of " <> T.pack
                (edhTypeNameOf badDtype)
            )
          , ( "shape"
            , \arg (dataDir', dataPath', dtype', _) ->
              Right (dataDir', dataPath', dtype', arg)
            )
          ]

aryMethods :: Unique -> EdhProgState -> STM [(AttrKey, EdhValue)]
aryMethods !classUniq !pgsModule =
  sequence
    $  [ (AttrByName nm, ) <$> mkHostProc scope vc nm hp mthArgs
       | (nm, vc, hp, mthArgs) <-
         [ ("[]", EdhMethod, aryIdxReadProc, PackReceiver [mandatoryArg "idx"])
         , ( "[=]"
           , EdhMethod
           , aryIdxWriteProc
           , PackReceiver [mandatoryArg "idx", mandatoryArg "val"]
           )
         , ("__repr__", EdhMethod, aryReprProc, PackReceiver [])
         ]
       ]
    ++ [ (AttrByName nm, ) <$> mkHostProperty scope nm getter setter
       | (nm, getter, setter) <-
         [ ("dir"  , aryDirGetter  , Nothing)
         , ("path" , aryPathGetter , Nothing)
         , ("dtype", aryDtypeGetter, Nothing)
         , ("size" , arySizeGetter , Nothing)
         , ("shape", aryShapeGetter, Nothing)
         , ("len1d", aryLen1dGetter, Just aryLen1dSetter)
         ]
       ]
 where
  !scope = contextScope $ edh'context pgsModule

  aryDirGetter :: EdhProcedure
  aryDirGetter _ !exit = withEntityOfClass classUniq
    $ \ !pgs !ary -> exitEdhSTM pgs exit $ EdhString $ db'array'dir ary

  aryPathGetter :: EdhProcedure
  aryPathGetter _ !exit = withEntityOfClass classUniq
    $ \ !pgs !ary -> exitEdhSTM pgs exit $ EdhString $ db'array'path ary

  aryDtypeGetter :: EdhProcedure
  aryDtypeGetter _ !exit = withEntityOfClass classUniq $ \ !pgs !ary ->
    exitEdhSTM pgs exit $ EdhString $ data'type'identifier $ db'array'dtype ary

  arySizeGetter :: EdhProcedure
  arySizeGetter _ !exit =
    withEntityOfClass classUniq $ \ !pgs (DbArray _ _ _ !das) ->
      readTMVar das >>= \case
        Right (!shape, _, _) ->
          exitEdhSTM pgs exit $ EdhDecimal $ fromIntegral $ dbArraySize shape
        Left !err -> throwSTM err

  aryShapeGetter :: EdhProcedure
  aryShapeGetter _ !exit =
    withEntityOfClass classUniq $ \ !pgs (DbArray _ _ _ !das) ->
      readTMVar das >>= \case
        Right (!shape, _, _) -> exitEdhSTM pgs exit $ edhArrayShape shape
        Left  !err           -> throwSTM err

  aryLen1dGetter :: EdhProcedure
  aryLen1dGetter _ !exit =
    withEntityOfClass classUniq $ \ !pgs (DbArray _ _ _ !das) ->
      readTMVar das >>= \case
        Right (_, !hdrPtr, _) ->
          edhPerformIO pgs (readDbArrayLength hdrPtr)
            $ exitEdhProc exit
            . EdhDecimal
            . fromIntegral
        Left !err -> throwSTM err

  aryLen1dSetter :: EdhProcedure
  aryLen1dSetter !apk !exit = case apk of
    ArgsPack [vlenV@(EdhDecimal !vlenN)] _ | vlenN >= 0 ->
      case D.decimalToInteger vlenN of
        Just !vlen ->
          withEntityOfClass classUniq $ \ !pgs (DbArray _ _ _ !das) ->
            readTMVar das >>= \case
              Right (_, !hdrPtr, _) -> do
                edhContIO pgs (writeDbArrayLength hdrPtr $ fromIntegral vlen)
                exitEdhSTM pgs exit vlenV
              Left !err -> throwSTM err
        Nothing ->
          throwEdh UsageError $ "Len1d should be integer, not: " <> T.pack
            (show vlenN)
    _ -> throwEdh UsageError $ "Invalid args: " <> T.pack (show apk)

  aryReprProc :: EdhProcedure
  aryReprProc _ !exit =
    withEntityOfClass classUniq
      $ \ !pgs (DbArray !dir !path (DataType !dti _) !das) ->
          readTMVar das >>= \case
            Left !err -> throwSTM err
            Right (!shape, _, _) ->
              exitEdhSTM pgs exit
                $  EdhString
                $  "DbArray("
                <> T.pack (show dir)
                <> ", "
                <> T.pack (show path)
                <> ", dtype="
                <> dti
                <> ", shape="
                <> T.pack (show shape)
                <> ")"


  aryIdxReadProc :: EdhProcedure
  aryIdxReadProc (ArgsPack !args _) !exit =
    withEntityOfClass classUniq
      $ \ !pgs (DbArray _ _ (DataType _dti !dts) !das) ->
          readTMVar das >>= \case
            Left  !err             -> throwSTM err
            Right (!shape, _, !fa) -> case args of
                -- TODO support slicing, of coz need to tell a slicing index from
                --      an element index first
              [EdhArgsPack (ArgsPack !idxs _)] ->
                flatIndexInShape pgs idxs shape $ \ !flatIdx ->
                  flat'array'read dts pgs (coerce fa) flatIdx
                    $ \ !rv -> exitEdhSTM pgs exit rv
              idxs -> flatIndexInShape pgs idxs shape $ \ !flatIdx ->
                flat'array'read dts pgs (coerce fa) flatIdx
                  $ \ !rv -> exitEdhSTM pgs exit rv


  aryIdxWriteProc :: EdhProcedure
  aryIdxWriteProc (ArgsPack !args _) !exit =
    withEntityOfClass classUniq
      $ \ !pgs (DbArray _ _ (DataType _dti !dts) !das) ->
          readTMVar das >>= \case
            Left  !err            -> throwSTM err
            Right (!shape, _, fa) -> case args of
                      -- TODO support slicing assign, of coz need to tell a slicing index
                      --      from an element index first
              [EdhArgsPack (ArgsPack !idxs _), !dv] ->
                flatIndexInShape pgs idxs shape $ \ !flatIdx ->
                  flat'array'write dts pgs (coerce fa) flatIdx dv
                    $ \ !rv -> exitEdhSTM pgs exit rv
              [idx, !dv] -> flatIndexInShape pgs [idx] shape $ \ !flatIdx ->
                flat'array'write dts pgs (coerce fa) flatIdx dv
                  $ \ !rv -> exitEdhSTM pgs exit rv
              -- TODO more friendly error msg
              _ -> throwEdhSTM pgs UsageError "Invalid index assign args"

