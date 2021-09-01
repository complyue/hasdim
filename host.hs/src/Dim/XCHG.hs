{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Dim.XCHG where

-- import           Debug.Trace

import qualified Data.Lossless.Decimal as D
import Data.Text (Text)
import qualified Data.Text as T
import Foreign (Bits, Int8, Storable)
import Language.Edh.EHI
import System.Random
import Type.Reflection
import Prelude

class Typeable t => EdhXchg t where
  edhDefaultValue :: t

  toEdh :: t -> Edh EdhValue

  fromEdh' :: EdhValue -> Edh (Maybe t)

  fromEdh :: EdhValue -> Edh t
  fromEdh v =
    fromEdh' v >>= \case
      Just t -> return t
      Nothing -> do
        !badDesc <- edhSimpleDescM v
        throwEdhM UsageError $
          "can not convert to host type `"
            <> T.pack (show $ typeRep @t)
            <> "` from value: "
            <> badDesc

instance EdhXchg EdhValue where
  edhDefaultValue = edhNA
  toEdh !v = return v
  fromEdh' !v = return $ Just v

instance EdhXchg D.Decimal where
  edhDefaultValue = D.nan
  toEdh !v = return $ EdhDecimal v
  fromEdh' !v = case edhUltimate v of
    (EdhDecimal !d) -> return $ Just d
    _ -> return Nothing

newtype YesNo = YesNo Int8
  deriving (Eq, Ord, Storable, Random, Num, Enum, Real, Integral, Bits)

yesOrNo :: Bool -> YesNo
yesOrNo b = YesNo $ if b then 1 else 0

instance {-# OVERLAPPABLE #-} EdhXchg YesNo where
  edhDefaultValue = YesNo 0
  toEdh (YesNo !b) = return $ EdhBool $ b /= 0
  fromEdh' !v =
    edhValueNullM v >>= \ !b ->
      return $ Just $ YesNo $ if b then 0 else 1

instance {-# OVERLAPPABLE #-} EdhXchg Text where
  edhDefaultValue = ""
  toEdh !s = return $ EdhString s
  fromEdh' (EdhString !s) = return $ Just s
  fromEdh' !v = Just <$> edhValueReprM v

instance {-# OVERLAPPABLE #-} EdhXchg Char where
  edhDefaultValue = '\0'
  toEdh !s = return $ EdhString $ T.singleton s
  fromEdh' !v = case edhUltimate v of
    EdhString !s -> case T.uncons s of
      Just (!c, _) -> return $ Just c
      Nothing -> return $ Just '\0'
    _ -> return Nothing

instance {-# OVERLAPPABLE #-} EdhXchg Double where
  edhDefaultValue = 0 / 0
  toEdh !n = return $ EdhDecimal $ D.decimalFromRealFloat n
  fromEdh' = coerceEdhToFloat

instance {-# OVERLAPPABLE #-} EdhXchg Float where
  edhDefaultValue = 0 / 0
  toEdh !n = return $ EdhDecimal $ D.decimalFromRealFloat n
  fromEdh' = coerceEdhToFloat

instance {-# OVERLAPPABLE #-} (Integral a, Typeable a) => EdhXchg a where
  edhDefaultValue = 0
  toEdh !n = return $ EdhDecimal $ fromIntegral n
  fromEdh' = coerceEdhToIntegral

instance Random Decimal where
  -- assuming not too many bits are needed with host decimal arrays
  -- device arrays can always be used to workaround the lack of random bits
  randomR (l, u) g =
    let (f, g') =
          randomR
            ( D.decimalToRealFloat l :: Float,
              D.decimalToRealFloat u :: Float
            )
            g
     in (D.decimalFromRealFloat f, g')
  random g =
    let (f :: Float, g') = random g
     in (D.decimalFromRealFloat f, g')

coerceEdhToFloat ::
  forall a.
  (RealFloat a) =>
  EdhValue ->
  Edh (Maybe a)
coerceEdhToFloat !v = case edhUltimate v of
  EdhDecimal !d -> return $ Just $ convertDecimal d
  EdhObject !o -> do
    !magicRtn <- callMagicM o (AttrByName "__float__") (ArgsPack [] odEmpty)
    case edhUltimate magicRtn of
      EdhDecimal !d -> return $ Just $ convertDecimal d
      _ ->
        edhSimpleDescM magicRtn >>= \ !badDesc ->
          throwEdhM UsageError $
            "bad value returned from __float__(): " <> badDesc
  _ -> return Nothing
  where
    convertDecimal :: Decimal -> a
    convertDecimal !d
      | D.decimalIsNaN d = 0 / 0
      | D.decimalIsInf d = if d < 0 then -1 else 1 / 0
      | otherwise = D.decimalToRealFloat d

coerceEdhToIntegral ::
  forall a.
  (Integral a) =>
  EdhValue ->
  Edh (Maybe a)
coerceEdhToIntegral !v = case edhUltimate v of
  EdhDecimal !d -> return $ convertDecimal d
  EdhObject !o -> do
    !magicRtn <- callMagicM o (AttrByName "__int__") (ArgsPack [] odEmpty)
    case edhUltimate magicRtn of
      EdhDecimal !d -> return $ convertDecimal d
      _ ->
        edhSimpleDescM magicRtn >>= \ !badDesc ->
          throwEdhM UsageError $
            "bad value returned from __int__(): " <> badDesc
  _ -> return Nothing
  where
    convertDecimal :: Decimal -> Maybe a
    convertDecimal !d = case D.decimalToInteger d of
      Just !i -> Just $ fromInteger i
      Nothing -> Nothing
