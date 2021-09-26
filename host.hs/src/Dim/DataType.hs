-- | Numpy dtype inspired abstraction for vectorizable types of data
module Dim.DataType where

-- import           Debug.Trace

import Control.Monad
import Data.Dynamic
import Data.Lossless.Decimal as D
import Data.Maybe
import Data.Typeable hiding (TypeRep, typeOf, typeRep)
import Dim.XCHG
import Foreign
import Language.Edh.MHI
import System.Random
import Type.Reflection
import Prelude

-- * DataType holding runtime representation & type class instances

-- | Device-native types stored in memory shared with computing devices
-- (a computing device can be a GPU or CPU with heavy SIMD orientation)
data DeviceDataType a = (Eq a, Storable a, EdhXchg a, Typeable a) =>
  DeviceDataType
  { device'data'type'ident :: !DataTypeIdent,
    device'data'type :: TypeRep a,
    with'num'device'data'type ::
      forall m r.
      (MonadPlus m) =>
      (forall a'. (a' ~ a, Num a', Ord a') => m r) ->
      m r,
    with'float'device'data'type ::
      forall m r.
      (MonadPlus m) =>
      (forall a'. (a' ~ a, RealFloat a') => m r) ->
      m r,
    with'random'device'data'type ::
      forall m r.
      (MonadPlus m) =>
      (forall a'. (a' ~ a, Random a', Ord a') => m r) ->
      m r
  }

instance Eq (DeviceDataType a) where
  x == y = device'data'type'ident x == device'data'type'ident y

-- | Lifted Haskell types directly operatable by the host language
data DirectDataType a = (Eq a, EdhXchg a, Typeable a) =>
  DirectDataType
  { direct'data'type'ident :: !DataTypeIdent,
    direct'data'default :: a,
    with'num'direct'data'type ::
      forall m r.
      (MonadPlus m) =>
      (forall a'. (a' ~ a, Num a', Ord a') => m r) ->
      m r,
    with'random'direct'data'type ::
      forall m r.
      (MonadPlus m) =>
      (forall a'. (a' ~ a, Random a', Ord a') => m r) ->
      m r,
    with'num'seed'direct'data'type ::
      forall m r.
      (MonadPlus m) =>
      ((D.Decimal -> a) -> m r) ->
      m r
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
  = (Eq a, Storable a, EdhXchg a, Typeable a) => DeviceDt !(DeviceDataType a)
  | (Eq a, EdhXchg a, Typeable a) => DirectDt !(DirectDataType a)
  | (Typeable a) => DummyDt !DataTypeIdent

data'type'ident :: DataType a -> DataTypeIdent
data'type'ident (DeviceDt dt) = device'data'type'ident dt
data'type'ident (DirectDt dt) = direct'data'type'ident dt
data'type'ident (DummyDt dti) = dti

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
  DummyDt dti'x -> case y of
    DummyDt dti'y -> case eqT of
      Just (Refl :: a :~: b) | dti'x == dti'y -> Just Refl
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
    DeviceDataType @a
      dti
      typeRep
      id
      id
      id

mkIntDataType ::
  forall a.
  (Integral a, Random a, Num a, Storable a, EdhXchg a, Typeable a) =>
  DataTypeIdent ->
  DataType a
mkIntDataType !dti =
  DeviceDt $
    DeviceDataType @a
      dti
      typeRep
      id
      (\_ -> mzero)
      id

mkBitsDataType ::
  forall a.
  (Bits a, Ord a, Storable a, EdhXchg a, Typeable a) =>
  DataTypeIdent ->
  DataType a
mkBitsDataType !dti =
  DeviceDt $
    DeviceDataType @a
      dti
      typeRep
      (\_ -> mzero)
      (\_ -> mzero)
      (\_ -> mzero)

mkBoxDataType ::
  forall a.
  (Eq a, EdhXchg a, Typeable a) =>
  DataTypeIdent ->
  a ->
  Maybe (D.Decimal -> a) ->
  DataType a
mkBoxDataType !dti !defv !maybeFromDec =
  DirectDt $
    DirectDataType @a
      dti
      defv
      (\_ -> mzero)
      (\_ -> mzero)
      $ case maybeFromDec of
        Nothing -> \_ -> mzero
        Just !fromDec -> ($ fromDec)

mkRealFracDataType ::
  forall a.
  (RealFrac a, Random a, Eq a, EdhXchg a, Typeable a) =>
  DataTypeIdent ->
  a ->
  Maybe (D.Decimal -> a) ->
  DataType a
mkRealFracDataType !dti !defv !maybeFromDec =
  DirectDt $
    DirectDataType @a
      dti
      defv
      id
      id
      $ case maybeFromDec of
        Nothing -> \_ -> mzero
        Just !fromDec -> ($ fromDec)

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
