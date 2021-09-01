-- | Numpy dtype inspired abstraction for vectorizable types of data
--
-- The data type system is extensible through the effect system of Edh
module Dim.DataType where

-- import           Debug.Trace

import Control.Applicative
import Control.Monad
import Data.Dynamic
import Data.Lossless.Decimal as D
import Data.Maybe
import Data.Typeable hiding (TypeRep, typeOf, typeRep)
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Storable.Mutable as MVS
import Dim.XCHG
import Foreign
import Foreign.ForeignPtr.Unsafe
import Language.Edh.EHI
import System.Random
import Type.Reflection
import Prelude

-- * DataType holding runtime representation & type class instances

-- | Device-native types stored in memory shared with computing devices
-- (a computing device can be a GPU or CPU with heavy SIMD orientation)
data DeviceDataType a' = DeviceDataType
  { device'data'type'ident :: !DataTypeIdent,
    device'data'type'holder ::
      forall r.
      ( forall a.
        (a ~ a', Eq a, Storable a, EdhXchg a, Typeable a) =>
        TypeRep a ->
        r
      ) ->
      r,
    device'data'type'as'of'num ::
      forall r.
      r ->
      ( forall a.
        (a ~ a', Num a, Eq a, Storable a, EdhXchg a, Typeable a) =>
        TypeRep a ->
        r
      ) ->
      r,
    device'data'type'as'of'float ::
      forall r.
      r ->
      ( forall a.
        (a ~ a', RealFloat a, Eq a, Storable a, EdhXchg a, Typeable a) =>
        TypeRep a ->
        r
      ) ->
      r,
    device'data'type'as'of'random ::
      forall r.
      r ->
      ( forall a.
        (a ~ a', Random a, Eq a, Ord a, Storable a, EdhXchg a, Typeable a) =>
        TypeRep a ->
        r
      ) ->
      r
  }

instance Eq (DeviceDataType a) where
  x == y = device'data'type'ident x == device'data'type'ident y

-- | Lifted Haskell types directly operatable by the host language
data DirectDataType a' = DirectDataType
  { direct'data'type'ident :: !DataTypeIdent,
    direct'data'defv'holder ::
      forall r.
      ( forall a.
        (a ~ a', Eq a, EdhXchg a, Typeable a) =>
        a ->
        r
      ) ->
      r,
    direct'data'type'as'of'num ::
      forall r.
      r ->
      ( forall a.
        (a ~ a', Num a, Eq a, EdhXchg a, Typeable a) =>
        TypeRep a ->
        r
      ) ->
      r,
    direct'data'type'as'of'random ::
      forall r.
      r ->
      ( forall a.
        (a ~ a', Random a, Eq a, Ord a, EdhXchg a, Typeable a) =>
        TypeRep a ->
        r
      ) ->
      r,
    direct'data'type'from'num ::
      forall r.
      r ->
      ( forall a.
        (a ~ a', Eq a, EdhXchg a, Typeable a) =>
        (D.Decimal -> a) ->
        r
      ) ->
      r
  }

instance Eq (DirectDataType a) where
  x == y = direct'data'type'ident x == direct'data'type'ident y

type DataTypeIdent = AttrName

-- | A data type conveys the representation as well as its relevant type class
-- instances to runtime, for dynamic linkage (i.e. high-performance execution)
-- in scripted fashion
--
-- note: need separate data constructors along respective ADTs because GHC does
--       not yet support impredicative polymorphism
data DataType a
  = (EdhXchg a, Typeable a) => DeviceDt !(DeviceDataType a)
  | (EdhXchg a, Typeable a) => DirectDt !(DirectDataType a)

data'type'ident :: DataType a -> DataTypeIdent
data'type'ident (DeviceDt dt) = device'data'type'ident dt
data'type'ident (DirectDt dt) = direct'data'type'ident dt

instance Eq (DataType a) where
  x == y = data'type'ident x == data'type'ident y

-- | Heterogeneous data type comparison
--
-- Also witness the equality of their encapsulated type, as with a positive
-- result
eqDataType :: forall a b. DataType a -> DataType b -> Maybe (a :~: b)
-- note: case-of pattern match is needed to bring the encapsulated type
--       parameter into scope, we need their witness of the 'Typeable' instance
--       so this function can be free of that constraint
eqDataType x y = case x of
  DeviceDt dt'x -> case y of
    DeviceDt dt'y -> case eqT of
      Just (Refl :: a :~: b) | dt'x == dt'y -> Just Refl
      _ -> Nothing
    _ -> Nothing
  DirectDt dt'x -> case y of
    DirectDt dt'y -> case eqT of
      Just (Refl :: a :~: b) | dt'x == dt'y -> Just Refl
      _ -> Nothing
    _ -> Nothing

{- HLINT ignore "Use const" -}

mkFloatDataType ::
  forall a.
  (RealFloat a, Random a, Num a, Storable a, EdhXchg a, Typeable a) =>
  DataTypeIdent ->
  DataType a
mkFloatDataType !dti =
  DeviceDt $
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
  DataType a
mkIntDataType !dti =
  DeviceDt $
    DeviceDataType
      dti
      ($ typeRep @a)
      (\_naExit exit -> exit (typeRep @a))
      (\naExit _exit -> naExit)
      (\_naExit exit -> exit (typeRep @a))

mkBitsDataType ::
  forall a.
  (Bits a, Ord a, Storable a, EdhXchg a, Typeable a) =>
  DataTypeIdent ->
  DataType a
mkBitsDataType !dti =
  DeviceDt $
    DeviceDataType
      dti
      ($ typeRep @a)
      (\naExit _exit -> naExit)
      (\naExit _exit -> naExit)
      (\naExit _exit -> naExit)

mkBoxDataType ::
  forall a.
  (Eq a, EdhXchg a, Typeable a) =>
  DataTypeIdent ->
  a ->
  Maybe (D.Decimal -> a) ->
  DataType a
mkBoxDataType !dti !defv !maybeFromDec =
  DirectDt $
    DirectDataType
      dti
      ($ defv)
      (\naExit _exit -> naExit)
      (\naExit _exit -> naExit)
      $ case maybeFromDec of
        Nothing -> \naExit _exit -> naExit
        Just !fromDec -> \_naExit exit -> exit fromDec

mkRealFracDataType ::
  forall a.
  (RealFrac a, Random a, Eq a, EdhXchg a, Typeable a) =>
  DataTypeIdent ->
  a ->
  Maybe (D.Decimal -> a) ->
  DataType a
mkRealFracDataType !dti !defv !maybeFromDec =
  DirectDt $
    DirectDataType
      dti
      ($ defv)
      (\_naExit exit -> exit (typeRep @a))
      (\_naExit exit -> exit (typeRep @a))
      $ case maybeFromDec of
        Nothing -> \naExit _exit -> naExit
        Just !fromDec -> \_naExit exit -> exit fromDec

withDataType ::
  forall m r.
  (MonadPlus m) =>
  Object ->
  (forall a. (Typeable a) => DataType a -> m r) ->
  m r
withDataType !dto !withDto = case edh'obj'store dto of
  HostStore (Dynamic trGDT monoDataType) -> case trGDT of
    App trDataType trA -> withTypeable trA $
      case trDataType `eqTypeRep` typeRep @DataType of
        Just HRefl -> withDto monoDataType
        _ -> mzero
    _ -> mzero
  _ -> mzero

dtypeEqProc :: EdhValue -> Edh EdhValue
dtypeEqProc !other = do
  !this <- edh'scope'this . contextScope . edh'context <$> edhThreadState
  case edhUltimate other of
    EdhObject !objOther -> (<|> rtnNeg) $
      withDataType objOther $ \ !dtOther ->
        withDataType this $ \ !dtSelf ->
          return $ EdhBool $ isJust $ dtOther `eqDataType` dtSelf
    _ -> rtnNeg
  where
    rtnNeg = return (EdhBool False)

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
    forall r. f a -> r -> ((Storable a) => ForeignPtr a -> r) -> r

data DeviceArray a = (Storable a, EdhXchg a, Typeable a) =>
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
  array'data'ptr (DeviceArray _cap fp) _naExit !exit = exit fp

data DirectArray a
  = (Eq a, EdhXchg a, Typeable a) => DirectArray !(MV.IOVector a)

instance FlatArray DirectArray a where
  array'capacity = directArrayCapacity
  array'duplicate = dupDirectArray
  array'reader (DirectArray iov) = \ !i -> MV.unsafeRead iov i
  array'writer (DirectArray iov) = \ !i !a -> MV.unsafeWrite iov i a
  array'data'ptr _a naExit _exit = naExit

emptyDeviceArray ::
  forall a. (EdhXchg a, Typeable a, Storable a) => IO (DeviceArray a)
emptyDeviceArray = do
  !np <- newForeignPtr_ nullPtr
  return $ DeviceArray @a 0 np

emptyDirectArray ::
  forall a. (Eq a, EdhXchg a, Typeable a) => IO (DirectArray a)
emptyDirectArray = do
  !iov <- MV.new 0
  return $ DirectArray @a iov

newDeviceArray ::
  forall a.
  (Eq a, Storable a, EdhXchg a, Typeable a) =>
  ArrayCapacity ->
  IO (ForeignPtr a, DeviceArray a)
newDeviceArray !cap = do
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
newDirectArray' !fill'val !cap = do
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
