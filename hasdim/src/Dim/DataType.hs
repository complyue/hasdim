
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
import qualified Data.HashMap.Strict           as Map
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
  deriving ( Typeable )

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

-- | host Class dtype()
dtypeCtor :: EdhHostCtor
-- not really constructable from Edh code, relies on host code to fill
-- the in-band storage
dtypeCtor _ _ !ctorExit = ctorExit $ toDyn nil

dtypeMethods :: EdhProgState -> STM [(AttrKey, EdhValue)]
dtypeMethods !pgsModule =
  sequence
    $  [ (AttrByName nm, ) <$> mkHostProc scope vc nm hp args
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
    ++ [ (AttrByName nm, ) <$> mkHostProperty scope nm getter setter
       | (nm, getter, setter) <- [("id", dtypeIdentProc, Nothing)]
       ]

 where
  !scope = contextScope $ edh'context pgsModule

  dtypeEqProc :: EdhProcedure
  dtypeEqProc (ArgsPack [EdhObject !dtoOther] _) !exit =
    withThatEntity $ \ !pgs (DataType !ident _) ->
      fromDynamic <$> readTVar (entity'store $ objEntity dtoOther) >>= \case
        Nothing -> exitEdhSTM pgs exit $ EdhBool False
        Just (DataType !identOther _) ->
          exitEdhSTM pgs exit $ EdhBool $ identOther == ident
  dtypeEqProc _ !exit = exitEdhProc exit $ EdhBool False

  dtypeIdentProc :: EdhProcedure
  dtypeIdentProc _ !exit =
    withThatEntity' (\ !pgs -> exitEdhSTM pgs exit $ EdhString "<bogus-dtype>")
      $ \ !pgs (DataType !ident _) -> exitEdhSTM pgs exit $ EdhString ident


-- | Resolve effective data storage routines per data type identifier
--
-- an exception is thrown if the identifier is not applicable
resolveDataType
  :: EdhProgState -> DataTypeIdent -> (DataType -> STM ()) -> STM ()
resolveDataType !pgs !dti =
  resolveDataType' pgs dti
    $  throwEdhSTM pgs UsageError
    $  "Not an applicable dtype: "
    <> dti
-- | Resolve effective data storage routines per data type identifier
-- 
-- will take the @naExit@ if the identifier is not applicable
resolveDataType'
  :: EdhProgState -> DataTypeIdent -> STM () -> (DataType -> STM ()) -> STM ()
resolveDataType' !pgs !dti !naExit !exit =
  runEdhProc pgs
    $ performEdhEffect (AttrBySym resolveDataTypeEffId) [EdhString dti] []
    $ \case
        EdhNil         -> contEdhSTM naExit
        EdhObject !dto -> contEdhSTM $ fromDynamic <$> objStore dto >>= \case
          Nothing  -> naExit
          Just !dt -> exit dt
        !badDtVal ->
          throwEdh UsageError
            $  "Bad return type from @resolveDataType(dti): "
            <> T.pack (edhTypeNameOf badDtVal)
resolveDataTypeEffId :: Symbol
resolveDataTypeEffId = globalSymbol "@resolveDataType"


-- | The ultimate fallback to have trivial data types resolved
resolveDataTypeProc :: Object -> EdhProcedure
resolveDataTypeProc !dtTmplObj (ArgsPack [EdhString !dti] !kwargs) !exit
  | Map.null kwargs = ask >>= \ !pgs -> contEdhSTM $ do
    let exitWith !dt =
          cloneEdhObject dtTmplObj (\_ !cloneExit -> cloneExit $ toDyn dt)
            $ \ !dto -> exitEdhSTM pgs exit $ EdhObject dto
    case dti of
      "float64" ->
        exitWith $ DataType dti (flatStorable :: FlatStorable Double)
      "float32" -> exitWith $ DataType dti (flatStorable :: FlatStorable Float)
      "int64"   -> exitWith $ DataType dti (flatStorable :: FlatStorable Int64)
      "int32"   -> exitWith $ DataType dti (flatStorable :: FlatStorable Int32)
      "int8"    -> exitWith $ DataType dti (flatStorable :: FlatStorable Int8)
      "byte"    -> exitWith $ DataType dti (flatStorable :: FlatStorable Word8)
      "intp"    -> exitWith $ DataType dti (flatStorable :: FlatStorable Int)
      "bool" -> exitWith $ DataType dti (flatStorable :: FlatStorable VecBool)
      _ ->
        throwEdhSTM pgs UsageError
          $  "A non-trivial data type requested,"
          <> " you may have some framework/lib to provide an effective dtype"
          <> " identified by: "
          <> dti
resolveDataTypeProc _ _ _ =
  throwEdh UsageError "Invalid args to @resolveDataType(dti)"


-- | FlatStorable facilitates the basic support of a data type to be managable
-- by HasDim, i.e. array allocation, element read/write, array bulk update.
--
-- More sophisticated, vectorized operations are supported by other collections
-- of routines, as they tends to have more demanding premises than required
-- here.
data FlatStorable a where
  FlatStorable ::(EdhXchg a, Storable a, Typeable a) => {
      flat'element'size :: Int
    , flat'element'align :: Int
    , flat'new'array :: EdhProgState
        -> Int -> (FlatArray a -> STM ()) -> STM ()
    , flat'grow'array :: EdhProgState
        -> FlatArray a -> Int -> (FlatArray a -> STM ()) -> STM ()
    , flat'array'read :: EdhProgState -> FlatArray a
        -> Int -> (EdhValue -> STM ()) -> STM ()
    , flat'array'write :: EdhProgState -> FlatArray a
        -> Int -> EdhValue -> (EdhValue -> STM ()) -> STM ()
    , flat'array'update :: EdhProgState
        -> [(Int,a)]  -> FlatArray a  -> STM () -> STM ()
  }-> FlatStorable a
 deriving Typeable
flatStorable
  :: forall a . (EdhXchg a, Storable a, Typeable a) => FlatStorable a
flatStorable = FlatStorable (sizeOf (undefined :: a))
                            (alignment (undefined :: a))
                            createArray
                            growArray
                            readArrayCell
                            writeArrayCell
                            updateArray
 where
  createArray !_ !cap !exit = unsafeIOToSTM (newFlatArray cap) >>= exit
  growArray _ (FlatArray !cap !fp) !newCap !exit = if newCap <= cap
    then exit $ FlatArray newCap fp
    else (exit =<<) $ unsafeIOToSTM $ do
      !p'  <- callocArray newCap
      !fp' <- newForeignPtr finalizerFree p'
      withForeignPtr fp $ \ !p -> copyArray p' p cap
      return $ FlatArray newCap fp'
  readArrayCell !pgs (FlatArray !cap !fp) !idx !exit =
    edhRegulateIndex pgs cap idx $ \ !posIdx -> do
      sv <- unsafeIOToSTM $ withForeignPtr fp $ \ !vPtr ->
        peekElemOff vPtr posIdx
      toEdh pgs sv $ \ !val -> exit val
  writeArrayCell !pgs (FlatArray !cap !fp) !idx !val !exit =
    edhRegulateIndex pgs cap idx $ \ !posIdx -> fromEdh pgs val $ \ !sv -> do
      unsafeIOToSTM $ withForeignPtr fp $ \ !vPtr -> pokeElemOff vPtr posIdx sv
      toEdh pgs sv $ \ !val' -> exit val'
  updateArray _ [] _ !exit = exit
  updateArray !pgs ((!idx, !sv) : rest'upds) ary@(FlatArray !cap !fp) !exit =
    edhRegulateIndex pgs cap idx $ \ !posIdx -> do
      unsafeIOToSTM $ withForeignPtr fp $ \ !vPtr -> pokeElemOff vPtr posIdx sv
      updateArray pgs rest'upds ary exit


-- | A pack of data manipulation routines, per operational category, per data
-- type identifier
data DataManiRoutinePack where
  DataManiRoutinePack ::{
      data'mpk'identifier :: DataTypeIdent
    , data'mpk'category :: Text
    , data'mpk'routines :: Dynamic
    } -> DataManiRoutinePack

-- | host Class dmrp()
dmrpCtor :: EdhHostCtor
-- not really constructable from Edh code, relies on host code to fill
-- the in-band storage
dmrpCtor _ _ !ctorExit = ctorExit $ toDyn nil

dmrpMethods :: EdhProgState -> STM [(AttrKey, EdhValue)]
dmrpMethods !pgsModule = sequence
  [ (AttrByName nm, ) <$> mkHostProc scope vc nm hp args
  | (nm, vc, hp, args) <-
    [("__repr__", EdhMethod, dmrpReprProc, PackReceiver [])]
  ]

 where
  !scope = contextScope $ edh'context pgsModule

  dmrpReprProc :: EdhProcedure
  dmrpReprProc _ !exit =
    withThatEntity' (\ !pgs -> exitEdhSTM pgs exit $ EdhString "<bogus-dmrp>")
      $ \ !pgs (DataManiRoutinePack !ident !cate _) ->
          exitEdhSTM pgs exit
            $  EdhString
            $  "<dmrp/"
            <> ident
            <> "#"
            <> cate
            <> ">"


data FlatOrd a where
  FlatOrd ::(Ord a, Storable a, Typeable a, EdhXchg a) => {
      flat'cmp'vectorized :: EdhProgState -> FlatArray a
        -> (Ordering -> Bool) -> EdhValue -> (FlatArray VecBool -> STM ()) -> STM ()
    , flat'cmp'element'wise :: EdhProgState -> FlatArray a
        -> (Ordering -> Bool) -> FlatArray a -> (FlatArray VecBool -> STM ()) -> STM ()
  }-> FlatOrd a
 deriving Typeable
flatOrd :: (Ord a, Storable a, Typeable a, EdhXchg a) => FlatOrd a
flatOrd = FlatOrd vecCmp elemCmp
 where
  -- vectorized comparation, yielding a new Int8 array
  vecCmp !pgs (FlatArray !cap !fp) !cmp !v !exit = fromEdh pgs v $ \ !sv ->
    (exit =<<) $ unsafeIOToSTM $ withForeignPtr fp $ \ !p -> do
      !rp  <- callocArray cap
      !rfp <- newForeignPtr finalizerFree rp
      let go i | i >= cap = return $ FlatArray cap rfp
          go i            = do
            ev <- peekElemOff p i
            pokeElemOff rp i $ if cmp $ compare ev sv then 1 else 0
            go (i + 1)
      go 0
  -- element-wise comparation, yielding a new Int8 array
  elemCmp _pgs (FlatArray !cap1 !fp1) !cmp (FlatArray _cap2 !fp2) !exit =
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
  => EdhProgState
  -> DataTypeIdent
  -> FlatArray a
  -> (FlatOrd a -> STM ())
  -> STM ()
resolveDataComparator !pgs !dti !fa =
  resolveDataComparator' pgs dti fa
    $  throwEdhSTM pgs UsageError
    $  "Ordering not supported by dtype: "
    <> dti
resolveDataComparator'
  :: forall a
   . (Typeable (FlatOrd a))
  => EdhProgState
  -> DataTypeIdent
  -> FlatArray a
  -> STM ()
  -> (FlatOrd a -> STM ())
  -> STM ()
resolveDataComparator' !pgs !dti _ !naExit !exit =
  runEdhProc pgs
    $ performEdhEffect (AttrBySym resolveDataComparatorEffId) [EdhString dti] []
    $ \case
        EdhNil -> contEdhSTM naExit
        EdhObject !dmrpo ->
          contEdhSTM $ fromDynamic <$> objStore dmrpo >>= \case
            Nothing -> naExit
            Just (DataManiRoutinePack _dmrp'dti _dmrp'cate !drp) ->
              case fromDynamic drp of
                Nothing  -> naExit
                Just !rp -> exit rp
        !badDtVal ->
          throwEdh UsageError
            $  "Bad return type from @resolveDataComparator(dti): "
            <> T.pack (edhTypeNameOf badDtVal)
resolveDataComparatorEffId :: Symbol
resolveDataComparatorEffId = globalSymbol "@resolveDataComparator"


-- | The ultimate fallback to have trivial data types resolved
resolveDataComparatorProc :: Object -> EdhProcedure
resolveDataComparatorProc !dmrpTmplObj (ArgsPack [EdhString !dti] !kwargs) !exit
  | Map.null kwargs = ask >>= \ !pgs -> contEdhSTM $ do
    let exitWith !drp =
          cloneEdhObject
              dmrpTmplObj
              (\_ !cloneExit ->
                cloneExit $ toDyn $ DataManiRoutinePack dti "cmp" drp
              )
            $ \ !dto -> exitEdhSTM pgs exit $ EdhObject dto
    case dti of
      "float64" -> exitWith $ toDyn (flatOrd :: FlatOrd Double)
      "float32" -> exitWith $ toDyn (flatOrd :: FlatOrd Float)
      "int64"   -> exitWith $ toDyn (flatOrd :: FlatOrd Int64)
      "int32"   -> exitWith $ toDyn (flatOrd :: FlatOrd Int32)
      "int8"    -> exitWith $ toDyn (flatOrd :: FlatOrd Int8)
      "byte"    -> exitWith $ toDyn (flatOrd :: FlatOrd Word8)
      "intp"    -> exitWith $ toDyn (flatOrd :: FlatOrd Int)
      "bool"    -> exitWith $ toDyn (flatOrd :: FlatOrd VecBool)
      _ ->
        throwEdhSTM pgs UsageError
          $  "A non-trivial data type requested,"
          <> " you may have some framework/lib to provide an effective dtype"
          <> " identified by: "
          <> dti
resolveDataComparatorProc _ _ _ =
  throwEdh UsageError "Invalid args to @resolveDataComparator(dti)"


data FlatOp a where
  FlatOp ::(EdhXchg a, Storable a, Typeable a) => {
      flat'op'vectorized :: EdhProgState -> FlatArray a
        -> Dynamic -> EdhValue -> (FlatArray a -> STM ()) -> STM ()
    , flat'op'element'wise :: EdhProgState -> FlatArray a
        -> Dynamic -> FlatArray a -> (FlatArray a -> STM ()) -> STM ()
    , flat'inp'vectorized :: EdhProgState -> FlatArray a
        -> Dynamic -> EdhValue -> STM () -> STM ()
    , flat'inp'vectorized'masked :: EdhProgState -> FlatArray VecBool -> FlatArray a
        -> Dynamic -> EdhValue -> STM () -> STM ()
    , flat'inp'element'wise :: EdhProgState -> FlatArray a
        -> Dynamic -> FlatArray a -> STM () -> STM ()
    , flat'inp'element'wise'masked :: EdhProgState ->  FlatArray VecBool -> FlatArray a
        -> Dynamic -> FlatArray a -> STM () -> STM ()
  }-> FlatOp a
 deriving Typeable
flatOp :: (EdhXchg a, Storable a, Typeable a) => FlatOp a
flatOp = FlatOp vecOp elemOp vecInp vecInpMasked elemInp elemInpMasked
 where
  -- vectorized operation, yielding a new array
  vecOp !pgs (FlatArray !cap !fp) !dop !v !exit = case fromDynamic dop of
    Nothing                  -> error "bug: dtype op type mismatch"
    Just (op :: a -> a -> a) -> fromEdh pgs v $ \ !sv ->
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
  elemOp _pgs (FlatArray !cap1 !fp1) !dop (FlatArray _cap2 !fp2) !exit =
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
  vecInp !pgs (FlatArray !cap !fp) !dop !v !exit = case fromDynamic dop of
    Nothing                  -> error "bug: dtype op type mismatch"
    Just (op :: a -> a -> a) -> fromEdh pgs v $ \ !sv ->
      (>> exit) $ unsafeIOToSTM $ withForeignPtr fp $ \ !p -> do
        let go i | i >= cap = return ()
            go i            = do
              ev <- peekElemOff p i
              pokeElemOff p i $ op ev sv
              go (i + 1)
        go 0
  -- vectorized operation, inplace modifying the array, with a bool mask
  vecInpMasked !pgs (FlatArray _cap !mfp) (FlatArray !cap !fp) !dop !v !exit =
    case fromDynamic dop of
      Nothing                  -> error "bug: dtype op type mismatch"
      Just (op :: a -> a -> a) -> fromEdh pgs v $ \ !sv ->
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
  -- element-wise operation, inplace modifying array
  elemInp _pgs (FlatArray !cap1 !fp1) !dop (FlatArray _cap2 !fp2) !exit =
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
  -- element-wise operation, inplace modifying array, with a bool mask
  elemInpMasked _pgs (FlatArray _cap !mfp) (FlatArray !cap1 !fp1) !dop (FlatArray _cap2 !fp2) !exit
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

resolveDataOperator
  :: forall a
   . (Typeable (FlatOp a))
  => EdhProgState
  -> DataTypeIdent
  -> FlatArray a
  -> (FlatOp a -> STM ())
  -> STM ()
resolveDataOperator !pgs !dti !fa =
  resolveDataOperator' pgs dti fa
    $  throwEdhSTM pgs UsageError
    $  "Operation not supported by dtype: "
    <> dti
resolveDataOperator'
  :: forall a
   . (Typeable (FlatOp a))
  => EdhProgState
  -> DataTypeIdent
  -> FlatArray a
  -> STM ()
  -> (FlatOp a -> STM ())
  -> STM ()
resolveDataOperator' !pgs !dti _ !naExit !exit =
  runEdhProc pgs
    $ performEdhEffect (AttrBySym resolveDataOperatorEffId) [EdhString dti] []
    $ \case
        EdhNil -> contEdhSTM naExit
        EdhObject !dmrpo ->
          contEdhSTM $ fromDynamic <$> objStore dmrpo >>= \case
            Nothing -> naExit
            Just (DataManiRoutinePack _dmrp'dti _dmrp'cate !drp) ->
              case fromDynamic drp of
                Nothing ->
                  throwEdhSTM pgs UsageError
                    $  "bug: data manipulation routine pack obtained for dtype "
                    <> dti
                    <> " mismatch the flat array type created from it."
                Just !rp -> exit rp
        !badDtVal ->
          throwEdh UsageError
            $  "Bad return type from @resolveDataOperator(dti): "
            <> T.pack (edhTypeNameOf badDtVal)
resolveDataOperatorEffId :: Symbol
resolveDataOperatorEffId = globalSymbol "@resolveDataOperator"


-- | The ultimate fallback to have trivial data types resolved
resolveDataOperatorProc :: Object -> EdhProcedure
resolveDataOperatorProc !dmrpTmplObj (ArgsPack [EdhString !dti] !kwargs) !exit
  | Map.null kwargs = ask >>= \ !pgs -> contEdhSTM $ do
    let exitWith !drp =
          cloneEdhObject
              dmrpTmplObj
              (\_ !cloneExit ->
                cloneExit $ toDyn $ DataManiRoutinePack dti "op" drp
              )
            $ \ !dto -> exitEdhSTM pgs exit $ EdhObject dto
    case dti of
      "float64" -> exitWith $ toDyn (flatOp :: FlatOp Double)
      "float32" -> exitWith $ toDyn (flatOp :: FlatOp Float)
      "int64"   -> exitWith $ toDyn (flatOp :: FlatOp Int64)
      "int32"   -> exitWith $ toDyn (flatOp :: FlatOp Int32)
      "int8"    -> exitWith $ toDyn (flatOp :: FlatOp Int8)
      "byte"    -> exitWith $ toDyn (flatOp :: FlatOp Word8)
      "intp"    -> exitWith $ toDyn (flatOp :: FlatOp Int)
      "bool"    -> exitWith $ toDyn (flatOp :: FlatOp VecBool)
      _ ->
        throwEdhSTM pgs UsageError
          $  "A non-trivial data type requested,"
          <> " you may have some framework/lib to provide an effective dtype"
          <> " identified by: "
          <> dti
resolveDataOperatorProc _ _ _ =
  throwEdh UsageError "Invalid args to @resolveDataOperator(dti)"


-- | host Class numdt()
numdtCtor :: EdhHostCtor
-- not really constructable from Edh code, relies on host code to fill
-- the in-band storage
numdtCtor _ _ !ctorExit = ctorExit $ toDyn nil

numdtMethods :: EdhProgState -> STM [(AttrKey, EdhValue)]
numdtMethods !pgsModule =
  sequence
    $  [ (AttrByName nm, ) <$> mkHostProc scope vc nm hp args
       | (nm, vc, hp, args) <-
         [ ("=="      , EdhMethod, numdtEqProc   , PackReceiver [])
         , ("__repr__", EdhMethod, numdtIdentProc, PackReceiver [])
         ]
       ]
    ++ [ (AttrByName nm, ) <$> mkHostProperty scope nm getter setter
       | (nm, getter, setter) <- [("id", numdtIdentProc, Nothing)]
       ]

 where
  !scope = contextScope $ edh'context pgsModule

  numdtEqProc :: EdhProcedure
  numdtEqProc (ArgsPack [EdhObject !dtoOther] _) !exit =
    withThatEntity $ \ !pgs (NumDataType !ident _) ->
      fromDynamic <$> readTVar (entity'store $ objEntity dtoOther) >>= \case
        Nothing -> exitEdhSTM pgs exit $ EdhBool False
        Just (NumDataType !identOther _) ->
          exitEdhSTM pgs exit $ EdhBool $ identOther == ident
  numdtEqProc _ !exit = exitEdhProc exit $ EdhBool False

  numdtIdentProc :: EdhProcedure
  numdtIdentProc _ !exit =
    withThatEntity' (\ !pgs -> exitEdhSTM pgs exit $ EdhString "<bogus-numdt>")
      $ \ !pgs (NumDataType !ident _) ->
          exitEdhSTM pgs exit $ EdhString $ "<numeric-dtype:" <> ident <> ">"


resolveNumDataType
  :: EdhProgState -> DataTypeIdent -> (NumDataType -> STM ()) -> STM ()
resolveNumDataType !pgs !dti =
  resolveNumDataType' pgs dti
    $  throwEdhSTM pgs UsageError
    $  "Not an applicable numeric dtype: "
    <> dti
resolveNumDataType'
  :: EdhProgState
  -> DataTypeIdent
  -> STM ()
  -> (NumDataType -> STM ())
  -> STM ()
resolveNumDataType' !pgs !dti !naExit !exit =
  runEdhProc pgs
    $ performEdhEffect (AttrBySym resolveNumDataTypeEffId) [EdhString dti] []
    $ \case
        EdhNil          -> contEdhSTM naExit
        EdhObject !ndto -> contEdhSTM $ fromDynamic <$> objStore ndto >>= \case
          Nothing   -> naExit
          Just !ndt -> exit ndt
        !badDtVal ->
          throwEdh UsageError
            $  "Bad return type from @resolveNumDataType(dti): "
            <> T.pack (edhTypeNameOf badDtVal)
resolveNumDataTypeEffId :: Symbol
resolveNumDataTypeEffId = globalSymbol "@resolveNumDataType"


-- | The ultimate fallback to have trivial data types resolved
resolveNumDataTypeProc :: Object -> EdhProcedure
resolveNumDataTypeProc !numdtTmplObj (ArgsPack [EdhString !dti] !kwargs) !exit
  | Map.null kwargs = ask >>= \ !pgs -> contEdhSTM $ do
    let exitWith !dndt =
          cloneEdhObject numdtTmplObj (\_ !cloneExit -> cloneExit dndt)
            $ \ !ndto -> exitEdhSTM pgs exit $ EdhObject ndto
    case dti of
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
        exitWith $ toDyn $ NumDataType dti (flatRanger :: FlatRanger Word8)
      "intp" ->
        exitWith $ toDyn $ NumDataType dti (flatRanger :: FlatRanger Int)
      -- todo should include bool ?
      -- "bool" ->
      --   exitWith $ toDyn $ NumDataType dti (flatRanger :: FlatRanger VecBool)
      _ ->
        throwEdhSTM pgs UsageError
          $  "A non-trivial numeric data type requested,"
          <> " you may have some framework/lib to provide an effective numdt"
          <> " identified by: "
          <> dti
resolveNumDataTypeProc _ _ _ =
  throwEdh UsageError "Invalid args to @resolveNumDataType(dti)"


data NumDataType where
  NumDataType ::(Num a, EdhXchg a, Storable a, Typeable a) => {
      num'type'identifier :: !DataTypeIdent
    , num'type'ranger :: !(FlatRanger a)
    } -> NumDataType


data FlatRanger a where
  FlatRanger ::(Num a, EdhXchg a, Storable a, Typeable a) => {
    flat'new'range'array :: EdhProgState
      -> Int -> Int -> Int -> (FlatArray a -> STM ()) -> STM ()
    }-> FlatRanger a
 deriving Typeable
flatRanger
  :: forall a . (Num a, EdhXchg a, Storable a, Typeable a) => FlatRanger a
flatRanger = FlatRanger rangeCreator
 where
  rangeCreator _ !start !stop _ !exit | stop == start = exit (emptyFlatArray @a)
  rangeCreator !pgs !start !stop !step !exit =
    if (stop > start && step <= 0) || (stop < start && step >= 0)
      then throwEdhSTM pgs UsageError "Range is not converging"
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

