module Dim.DbArray where

-- import           Debug.Trace

import Control.Applicative
import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import Data.Dynamic
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE
import qualified Data.Lossless.Decimal as D
import Data.Text (Text)
import qualified Data.Text as T
import Dim.FlatArray
import Event.Analytics.EHI
import Foreign hiding (void)
import Language.Edh.EHI
import System.FilePath
import System.IO
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

-- | Disk backed array
data DbArray a
  = (Eq a, Storable a, EdhXchg a, Typeable a) =>
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
mmapDbArray !asVar !dataDir !dataPath !maybeShape !overwrite =
  handle (atomically . void . tryPutTMVar asVar . Left) $ case maybeShape of
    Just !shape -> do
      (dbaHdr, dba) <- mmapDBA dataFilePath (Just $ dbArraySize shape) overwrite
      atomically $ do
        void $ tryTakeTMVar asVar
        void $ tryPutTMVar asVar $ Right (shape, dbaHdr, dba)
    Nothing -> do
      (dbaHdr, dba) <- mmapDBA dataFilePath Nothing overwrite
      atomically $ do
        void $ tryTakeTMVar asVar
        void $
          tryPutTMVar asVar $
            Right
              ( ArrayShape (("", device'array'cap dba) :| []),
                dbaHdr,
                dba
              )
  where
    !dataFilePath = T.unpack dataDir </> T.unpack (dataPath <> ".dba")

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
asDbArrayOf !obj !exit = case objDynamicValue obj of
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

withDbArrayOf :: forall a. (Typeable a) => Object -> Edh (Object, DbArray a)
withDbArrayOf !obj = do
  supers <- readTVarEdh $ edh'obj'supers obj
  withComposition $ obj : supers
  where
    withComposition :: [Object] -> Edh (Object, DbArray a)
    withComposition [] = naM ""
    withComposition (o : rest) =
      asDbArrayOf @a o (return . (o,)) <|> withComposition rest

withDbArrayOf' :: forall a. (Typeable a) => EdhValue -> Edh (Object, DbArray a)
withDbArrayOf' !val = case edhUltimate val of
  EdhObject !obj -> do
    withDbArrayOf obj
  _ -> naM ""

withDbArraySelfOf :: forall a. (Typeable a) => Edh (Object, DbArray a)
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
    withComposition (o : rest) = case objDynamicValue o of
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
