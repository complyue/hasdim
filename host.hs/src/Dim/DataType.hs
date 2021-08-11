{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Numpy dtype inspired abstraction for vectorizable types of data
--
-- The data type system is extensible through the effect system of Edh
module Dim.DataType where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Monad
import Data.Dynamic
import qualified Data.Lossless.Decimal as D
import Data.Maybe
import Data.Text (Text)
import Data.Typeable hiding (TypeRep, typeOf, typeRep)
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Storable.Mutable as MVS
import Dim.XCHG
import Foreign as F
import Foreign.ForeignPtr.Unsafe
import Language.Edh.EHI
import Type.Reflection
import Prelude

-- * DataType holding runtime representation

type DataTypeIdent = AttrName

data DeviceDataType = DeviceDataType
  { device'data'type'ident :: !DataTypeIdent,
    device'data'type'holder ::
      forall r.
      (forall a. (EdhXchg a, Storable a, Typeable a) => TypeRep a -> r) ->
      r,
    device'data'type'as'of'num ::
      forall r.
      r ->
      ( forall a.
        (Num a, EdhXchg a, Storable a, Typeable a) =>
        TypeRep a ->
        r
      ) ->
      r,
    device'data'type'as'of'int ::
      forall r.
      r ->
      ( forall a.
        (Integral a, EdhXchg a, Storable a, Typeable a) =>
        TypeRep a ->
        r
      ) ->
      r,
    device'data'type'as'of'float ::
      forall r.
      r ->
      ( forall a.
        (RealFloat a, EdhXchg a, Storable a, Typeable a) =>
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

mkIntDataType ::
  forall a.
  (Integral a, Num a, Storable a, EdhXchg a, Typeable a) =>
  DataTypeIdent ->
  DeviceDataType
mkIntDataType !dti =
  DeviceDataType
    dti
    ($ typeRep @a)
    (\_naExit exit -> exit (typeRep @a))
    (\_naExit exit -> exit (typeRep @a))
    (\naExit _exit -> naExit)

mkFloatDataType ::
  forall a.
  (RealFloat a, Num a, Storable a, EdhXchg a, Typeable a) =>
  DataTypeIdent ->
  DeviceDataType
mkFloatDataType !dti =
  DeviceDataType
    dti
    ($ typeRep @a)
    (\_naExit exit -> exit (typeRep @a))
    (\naExit _exit -> naExit)
    (\_naExit exit -> exit (typeRep @a))

data DirectDataType = DirectDataType
  { direct'data'type'ident :: !DataTypeIdent,
    direct'data'defv'holder ::
      forall r.
      (forall a. (EdhXchg a, Eq a, Typeable a) => a -> r) ->
      r,
    direct'data'type'as'of'frac ::
      forall r.
      r ->
      ( forall a.
        (RealFrac a, EdhXchg a, Eq a, Typeable a) =>
        TypeRep a ->
        r
      ) ->
      r
  }

instance Eq DirectDataType where
  (DirectDataType x'dti x'dvh _) == (DirectDataType y'dti y'dvh _) =
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
mkBoxDataType !dti !def'val =
  DirectDataType
    dti
    ($ def'val)
    (\naExit _exit -> naExit)

mkRealFracDataType ::
  forall a.
  (RealFrac a, Eq a, EdhXchg a, Typeable a) =>
  DataTypeIdent ->
  a ->
  DirectDataType
mkRealFracDataType !dti !def'val =
  DirectDataType
    dti
    ($ def'val)
    (\_naExit exit -> exit (typeRep @a))

withDeviceDataType ::
  forall m.
  Monad m =>
  Object ->
  m () ->
  (forall a. (EdhXchg a, Storable a, Typeable a) => TypeRep a -> m ()) ->
  m ()
withDeviceDataType !dto !naExit !exit = case edh'obj'store dto of
  HostStore (Dynamic trDataType monoDataType) ->
    case trDataType `eqTypeRep` typeRep @DeviceDataType of
      Just HRefl -> device'data'type'holder monoDataType exit
      _ -> naExit
  _ -> naExit

withDirectDataType ::
  forall m.
  Monad m =>
  Object ->
  m () ->
  (forall a. (EdhXchg a, Eq a, Typeable a) => a -> m ()) ->
  m ()
withDirectDataType !dto !naExit !exit = case edh'obj'store dto of
  HostStore (Dynamic trDataType monoDataType) ->
    case trDataType `eqTypeRep` typeRep @DirectDataType of
      Just HRefl -> direct'data'defv'holder monoDataType exit
      _ -> naExit
  _ -> naExit

withDataType ::
  forall m.
  Monad m =>
  Object ->
  m () ->
  (DeviceDataType -> m ()) ->
  (DirectDataType -> m ()) ->
  m ()
withDataType !dto !naExit !devExit !dirExit = case edh'obj'store dto of
  HostStore (Dynamic trDataType monoDataType) ->
    case trDataType `eqTypeRep` typeRep @DeviceDataType of
      Just HRefl -> devExit monoDataType
      _ -> case trDataType `eqTypeRep` typeRep @DirectDataType of
        Just HRefl -> dirExit monoDataType
        _ -> naExit
  _ -> naExit

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
    dtypeAllocator :: "dti" ?: Text -> EdhObjectAllocator
    dtypeAllocator (optionalArg -> !maybeDti) !ctorExit !ets = case maybeDti of
      Nothing -> box
      Just "float64" -> f8
      Just "f8" -> f8
      Just "float32" -> f4
      Just "f4" -> f4
      Just "intp" -> intp
      Just "int64" -> i8
      Just "i8" -> i8
      Just "int32" -> i4
      Just "i4" -> i4
      Just "int8" -> i1
      Just "i1" -> i1
      Just "bool" -> yesno
      Just "yesno" -> yesno
      Just "box" -> box
      Just "object" -> box -- for Python Numpy compatibility
      Just "decimal" -> decimal
      Just badDti -> throwEdh ets UsageError $ "invalid dtype id: " <> badDti
      where
        f8 =
          ctorExit Nothing $
            HostStore $ toDyn $ mkFloatDataType @Double "float64"
        f4 =
          ctorExit Nothing $
            HostStore $ toDyn $ mkFloatDataType @Float "float32"
        intp =
          ctorExit Nothing $
            HostStore $ toDyn $ mkIntDataType @Int "intp"
        i8 =
          ctorExit Nothing $
            HostStore $ toDyn $ mkIntDataType @Int64 "int64"
        i4 =
          ctorExit Nothing $
            HostStore $ toDyn $ mkIntDataType @Int32 "int32"
        i1 =
          ctorExit Nothing $
            HostStore $ toDyn $ mkIntDataType @Int8 "int8"
        yesno =
          ctorExit Nothing $
            HostStore $ toDyn $ mkIntDataType @YesNo "yesno"
        box =
          ctorExit Nothing $
            HostStore $ toDyn $ mkBoxDataType @EdhValue "box" edhNA
        decimal =
          ctorExit Nothing $
            HostStore $ toDyn $ mkRealFracDataType @Decimal "decimal" D.nan

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

    dtypeIdentProc :: EdhHostProc
    dtypeIdentProc !exit !ets =
      withDataType
        this
        badThis
        (exitEdh ets exit . EdhString . device'data'type'ident)
        (exitEdh ets exit . EdhString . direct'data'type'ident)
      where
        this = edh'scope'this $ contextScope $ edh'context ets

        badThis = throwEdh ets EvalError "bug: not a host value of dtype"

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

data DirectArray a
  = (EdhXchg a, Typeable a) => DirectArray !(MV.IOVector a)

instance FlatArray DirectArray a where
  array'capacity = directArrayCapacity
  array'duplicate = dupDirectArray
  array'reader (DirectArray iov) = \ !i -> MV.unsafeRead iov i
  array'writer (DirectArray iov) = \ !i !a -> MV.unsafeWrite iov i a

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
  (EdhXchg a, Typeable a, Storable a) =>
  ArrayCapacity ->
  IO (ForeignPtr a, DeviceArray a)
newDeviceArray !cap = do
  !p <- callocArray @a cap
  !fp <- newForeignPtr finalizerFree p
  return (fp, DeviceArray @a cap fp)

newDirectArray ::
  forall a.
  (EdhXchg a, Typeable a) =>
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
