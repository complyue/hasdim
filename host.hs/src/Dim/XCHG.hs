{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Dim.XCHG where

-- import           Debug.Trace

import Control.Concurrent.STM (STM)
-- import           Data.Bits

import qualified Data.Lossless.Decimal as D
import Data.Text (Text)
import qualified Data.Text as T
import Foreign (Bits, Int8, Storable)
import Language.Edh.EHI
import System.Random
import Prelude

class EdhXchg t where
  toEdh :: t -> EdhTxExit EdhValue -> EdhTx
  fromEdh :: EdhValue -> EdhTxExit t -> EdhTx

instance EdhXchg EdhValue where
  toEdh !v !exit = exit v
  fromEdh !v !exit = exit v

instance EdhXchg D.Decimal where
  toEdh !v !exit = exit $ EdhDecimal v
  fromEdh (EdhDecimal !v) !exit = exit v
  fromEdh _ !exit = exit D.nan

newtype YesNo = YesNo Int8
  deriving (Eq, Ord, Storable, Num, Enum, Real, Integral, Bits)

instance {-# OVERLAPPABLE #-} EdhXchg YesNo where
  toEdh (YesNo !b) !exit = exit $ EdhBool $ b /= 0
  fromEdh !v !exit =
    edhValueNullTx v $ \ !b -> exit $ YesNo $ if b then 0 else 1

instance {-# OVERLAPPABLE #-} EdhXchg Text where
  toEdh !s !exit = exit $ EdhString s
  fromEdh (EdhString !s) !exit = exit s
  fromEdh !v !exit = edhValueReprTx v exit

instance {-# OVERLAPPABLE #-} EdhXchg Char where
  toEdh !s !exit = exit $ EdhString $ T.singleton s
  fromEdh (EdhString !s) !exit = case T.uncons s of
    Just (!c, _) -> exit c
    Nothing -> exit '\0'
  fromEdh !v !exit = edhValueReprTx v $ \ !s -> case T.uncons s of
    Just (!c, _) -> exit c
    Nothing -> exit '\0'

instance {-# OVERLAPPABLE #-} EdhXchg Double where
  toEdh !n !exit = exit $ EdhDecimal $ D.decimalFromRealFloat n
  fromEdh !v !exit = coerceEdhToFloat v exit

instance {-# OVERLAPPABLE #-} EdhXchg Float where
  toEdh !n !exit = exit $ EdhDecimal $ D.decimalFromRealFloat n
  fromEdh !v !exit = coerceEdhToFloat v exit

instance {-# OVERLAPPABLE #-} (Integral a) => EdhXchg a where
  toEdh !n !exit = exit $ EdhDecimal $ fromIntegral n
  fromEdh !v !exit = coerceEdhToIntegral v exit

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

coerceEdhToFloat :: (RealFloat a) => EdhValue -> EdhTxExit a -> EdhTx
coerceEdhToFloat !v =
  coerceEdhToFloat' v $
    edhValueReprTx v $ \ !r ->
      throwEdhTx UsageError $
        "float expected but given a " <> edhTypeNameOf v <> ": " <> r

coerceEdhToFloat' ::
  (RealFloat a) => EdhValue -> EdhTx -> EdhTxExit a -> EdhTx
coerceEdhToFloat' !v !naExit !exit !ets = case edhUltimate v of
  EdhDecimal !d -> exitWith d
  EdhObject !o ->
    lookupEdhObjMagic o (AttrByName "__float__") >>= \case
      (_, EdhNil) -> runEdhTx ets naExit
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
  _ -> runEdhTx ets naExit
  where
    exitWithMagicResult :: EdhTxExit EdhValue
    exitWithMagicResult (EdhDecimal !d) _ets = exitWith d
    exitWithMagicResult !badVal _ets = edhValueDesc ets badVal $ \ !badDesc ->
      throwEdh ets UsageError $
        "bad value returned from __float__(): " <> badDesc
    exitWith :: Decimal -> STM ()
    exitWith !d
      | D.decimalIsNaN d =
        exitEdh ets exit (0 / 0)
    exitWith !d
      | D.decimalIsInf d =
        exitEdh ets exit (if d < 0 then -1 else 1 / 0)
    exitWith !d =
      exitEdh ets exit $ D.decimalToRealFloat d

coerceEdhToIntegral ::
  (Integral a) => EdhValue -> EdhTxExit a -> EdhTx
coerceEdhToIntegral !v =
  coerceEdhToIntegral' v $
    edhValueReprTx v $ \ !r ->
      throwEdhTx UsageError $
        "integer expected but given a " <> edhTypeNameOf v <> ": " <> r

coerceEdhToIntegral' ::
  (Integral a) => EdhValue -> EdhTx -> EdhTxExit a -> EdhTx
coerceEdhToIntegral' !v !naExit !exit !ets = case edhUltimate v of
  EdhDecimal !d -> exitWith d
  EdhObject !o ->
    lookupEdhObjMagic o (AttrByName "__int__") >>= \case
      (_, EdhNil) -> runEdhTx ets naExit
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
  _ -> runEdhTx ets naExit
  where
    exitWithMagicResult :: EdhTxExit EdhValue
    exitWithMagicResult (EdhDecimal !d) _ets = exitWith d
    exitWithMagicResult !badVal _ets = edhValueDesc ets badVal $ \ !badDesc ->
      throwEdh ets UsageError $ "bad value returned from __int__(): " <> badDesc
    exitWith :: Decimal -> STM ()
    exitWith !d = case D.decimalToInteger d of
      Just !i -> exitEdh ets exit $ fromInteger i
      Nothing -> runEdhTx ets naExit
