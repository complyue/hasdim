{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Dim.XCHG where

-- import           Debug.Trace

import Control.Concurrent.STM (STM)
-- import           Data.Bits

import Data.Dynamic (Typeable)
import qualified Data.Lossless.Decimal as D
import Data.Text (Text)
import qualified Data.Text as T
import Foreign (Bits, Int8, Storable)
import Language.Edh.EHI
import System.Random
import Prelude

class EdhXchg t where
  toEdh :: EdhThreadState -> t -> (EdhValue -> STM ()) -> STM ()
  fromEdh :: EdhThreadState -> EdhValue -> (t -> STM ()) -> STM ()

instance EdhXchg EdhValue where
  toEdh _ets !v !exit = exit v
  fromEdh _ets !v !exit = exit v

instance EdhXchg D.Decimal where
  toEdh _ets !v !exit = exit $ EdhDecimal v
  fromEdh _ets (EdhDecimal !v) !exit = exit v
  fromEdh _ets _ !exit = exit D.nan

newtype YesNo = YesNo Int8
  deriving (Eq, Ord, Storable, Num, Bits, Typeable)

instance {-# OVERLAPPABLE #-} EdhXchg YesNo where
  toEdh _ets (YesNo !b) !exit = exit $ EdhBool $ b /= 0
  fromEdh !ets !v !exit =
    edhValueNull ets v $ \ !b -> exit $ YesNo $ if b then 0 else 1

instance {-# OVERLAPPABLE #-} EdhXchg Text where
  toEdh _ets !s !exit = exit $ EdhString s
  fromEdh _ets (EdhString !s) !exit = exit s
  fromEdh !ets !v !exit = edhValueRepr ets v exit

instance {-# OVERLAPPABLE #-} EdhXchg Char where
  toEdh _ets !s !exit = exit $ EdhString $ T.singleton s
  fromEdh _ets (EdhString !s) !exit = case T.uncons s of
    Just (!c, _) -> exit c
    Nothing -> exit '\0'
  fromEdh !ets !v !exit = edhValueRepr ets v $ \ !s -> case T.uncons s of
    Just (!c, _) -> exit c
    Nothing -> exit '\0'

instance {-# OVERLAPPABLE #-} EdhXchg Double where
  toEdh _ets !n !exit = exit $ EdhDecimal $ D.decimalFromRealFloat n
  fromEdh !ets !v !exit = coerceEdhToFloat ets v exit

instance {-# OVERLAPPABLE #-} EdhXchg Float where
  toEdh _ets !n !exit = exit $ EdhDecimal $ D.decimalFromRealFloat n
  fromEdh !ets !v !exit = coerceEdhToFloat ets v exit

instance {-# OVERLAPPABLE #-} (Integral a) => EdhXchg a where
  toEdh _ets !n !exit = exit $ EdhDecimal $ fromIntegral n
  fromEdh !ets !v !exit = coerceEdhToIntegral ets v exit

instance Random Decimal where
  -- assuming not too many bits are needed with host decimal arrays
  -- device arrays can always be used to workaround the lack of random bits
  randomR (l, u) g =
    let (f, g') =
          randomR
            ( (fromRational $ toRational l) :: Float,
              (fromRational $ toRational u) :: Float
            )
            g
     in (fromRational $ toRational f, g')
  random g =
    let (f :: Float, g') = random g
     in (fromRational $ toRational f, g')

coerceEdhToFloat ::
  (RealFloat a) => EdhThreadState -> EdhValue -> (a -> STM ()) -> STM ()
coerceEdhToFloat !ets !v =
  coerceEdhToFloat' ets v $
    edhValueRepr ets v $ \ !r ->
      throwEdh ets UsageError $
        "float expected but given a " <> edhTypeNameOf v <> ": " <> r

coerceEdhToFloat' ::
  (RealFloat a) =>
  EdhThreadState ->
  EdhValue ->
  STM () ->
  (a -> STM ()) ->
  STM ()
coerceEdhToFloat' !ets !v !naExit !exit = case edhUltimate v of
  EdhDecimal !d -> exitWith d
  EdhObject !o ->
    lookupEdhObjMagic o (AttrByName "__float__") >>= \case
      (_, EdhNil) -> naExit
      (_, EdhDecimal !d) -> exitWith d
      (!this', EdhProcedure (EdhMethod !mth) _) ->
        runEdhTx ets $
          callEdhMethod this' o mth (ArgsPack [] odEmpty) id exitWithMagicResult
      (_, EdhBoundProc (EdhMethod !mth) !this !that _) ->
        runEdhTx ets $
          callEdhMethod
            this
            that
            mth
            (ArgsPack [] odEmpty)
            id
            exitWithMagicResult
      (_, !badMagic) -> edhValueDesc ets badMagic $ \ !badDesc ->
        throwEdh ets UsageError $ "malformed __float__ magic: " <> badDesc
  _ -> naExit
  where
    exitWithMagicResult :: EdhTxExit EdhValue
    exitWithMagicResult (EdhDecimal !d) _ets = exitWith d
    exitWithMagicResult !badVal _ets = edhValueDesc ets badVal $ \ !badDesc ->
      throwEdh ets UsageError $ "bad value returned from __float__(): " <> badDesc
    exitWith :: Decimal -> STM ()
    exitWith !d | D.decimalIsNaN d = exit (0 / 0)
    exitWith !d | D.decimalIsInf d = exit (if d < 0 then -1 else 1 / 0)
    exitWith !d = exit $ fromRational $ toRational d

coerceEdhToIntegral ::
  (Integral a) => EdhThreadState -> EdhValue -> (a -> STM ()) -> STM ()
coerceEdhToIntegral !ets !v =
  coerceEdhToIntegral' ets v $
    edhValueRepr ets v $ \ !r ->
      throwEdh ets UsageError $
        "integer expected but given a " <> edhTypeNameOf v <> ": " <> r

coerceEdhToIntegral' ::
  (Integral a) =>
  EdhThreadState ->
  EdhValue ->
  STM () ->
  (a -> STM ()) ->
  STM ()
coerceEdhToIntegral' !ets !v !naExit !exit = case edhUltimate v of
  EdhDecimal !d -> exitWith d
  EdhObject !o ->
    lookupEdhObjMagic o (AttrByName "__int__") >>= \case
      (_, EdhNil) -> naExit
      (_, EdhDecimal !d) -> exitWith d
      (!this', EdhProcedure (EdhMethod !mth) _) ->
        runEdhTx ets $
          callEdhMethod this' o mth (ArgsPack [] odEmpty) id exitWithMagicResult
      (_, EdhBoundProc (EdhMethod !mth) !this !that _) ->
        runEdhTx ets $
          callEdhMethod
            this
            that
            mth
            (ArgsPack [] odEmpty)
            id
            exitWithMagicResult
      (_, !badMagic) -> edhValueDesc ets badMagic $ \ !badDesc ->
        throwEdh ets UsageError $ "malformed __int__ magic: " <> badDesc
  _ -> naExit
  where
    exitWithMagicResult :: EdhTxExit EdhValue
    exitWithMagicResult (EdhDecimal !d) _ets = exitWith d
    exitWithMagicResult !badVal _ets = edhValueDesc ets badVal $ \ !badDesc ->
      throwEdh ets UsageError $ "bad value returned from __int__(): " <> badDesc
    exitWith :: Decimal -> STM ()
    exitWith !d = case D.decimalToInteger d of
      Just !i -> exit $ fromInteger i
      Nothing -> naExit
