{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Dim.XCHG where

import           Prelude
-- import           Debug.Trace

import           Foreign

import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import qualified Data.Text                     as T

import           Data.Dynamic

import           Data.Scientific

import           Data.Lossless.Decimal         as D

import           Language.Edh.EHI


class EdhXchg t where
  toEdh :: EdhProgState -> t -> (EdhValue -> STM ()) -> STM ()
  fromEdh :: EdhProgState  -> EdhValue -> (t -> STM ()) -> STM ()


newtype VecBool = VecBool Int8
  deriving (Eq, Ord, Storable, Typeable)

instance {-# OVERLAPPABLE #-} EdhXchg VecBool where
  toEdh _pgs (VecBool !b) !exit = exit $ EdhBool $ b /= 0
  fromEdh !pgs !v !exit =
    edhValueNull pgs v $ \ !b -> exit $ VecBool $ if b then 0 else 1


instance {-# OVERLAPPABLE #-} EdhXchg Text where
  toEdh _pgs !s !exit = exit $ EdhString s
  fromEdh _pgs (EdhString !s) !exit = exit s
  fromEdh !pgs !v             !exit = edhValueReprSTM pgs v exit


instance {-# OVERLAPPABLE #-} EdhXchg Char where
  toEdh _pgs !s !exit = exit $ EdhString $ T.singleton s
  fromEdh _pgs (EdhString !s) !exit = case T.uncons s of
    Just (!c, _) -> exit c
    Nothing      -> exit '\0'
  fromEdh !pgs !v !exit = edhValueReprSTM pgs v $ \ !s -> case T.uncons s of
    Just (!c, _) -> exit c
    Nothing      -> exit '\0'


instance {-# OVERLAPPABLE #-} EdhXchg Double where
  toEdh _pgs !n !exit =
    exit $ EdhDecimal $ D.decimalFromScientific $ fromFloatDigits n
  fromEdh !pgs !v !exit = coerceEdhToFloat pgs v exit

instance {-# OVERLAPPABLE #-} EdhXchg Float where
  toEdh _pgs !n !exit =
    exit $ EdhDecimal $ D.decimalFromScientific $ fromFloatDigits n
  fromEdh !pgs !v !exit = coerceEdhToFloat pgs v exit


instance {-# OVERLAPPABLE #-} (Integral a) => EdhXchg a where
  toEdh _pgs !n !exit = exit $ EdhDecimal $ fromIntegral n
  fromEdh !pgs !v !exit = coerceEdhToIntegral pgs v exit


coerceEdhToFloat
  :: (RealFloat a) => EdhProgState -> EdhValue -> (a -> STM ()) -> STM ()
coerceEdhToFloat !pgs !v =
  coerceEdhToFloat' pgs v
    $  throwEdhSTM pgs UsageError
    $  "Float expected but given a "
    <> T.pack (edhTypeNameOf v)
coerceEdhToFloat'
  :: (RealFloat a)
  => EdhProgState
  -> EdhValue
  -> STM ()
  -> (a -> STM ())
  -> STM ()
coerceEdhToFloat' !pgs !v !naExit !exit = case edhUltimate v of
  EdhDecimal !n -> exit $ fromRational $ toRational n
  EdhObject  !o -> lookupEdhObjAttr pgs o (AttrByName "__float__") >>= \case
    EdhNil -> naExit
    EdhMethod !mth ->
      runEdhProc pgs
        $ callEdhMethod o mth (ArgsPack [] mempty) id
        $ \(OriginalValue !rtn _ _) -> case edhUltimate rtn of
            EdhDecimal !n -> contEdhSTM $ exit $ fromRational $ toRational n
            !badVal ->
              throwEdh UsageError
                $  "bug: bad value returned from __float__ magic: "
                <> T.pack (edhTypeNameOf badVal)
    !badMagic ->
      throwEdhSTM pgs UsageError $ "Malformed __float__ magic: " <> T.pack
        (edhTypeNameOf badMagic)
  _ -> naExit

coerceEdhToIntegral
  :: (Integral a) => EdhProgState -> EdhValue -> (a -> STM ()) -> STM ()
coerceEdhToIntegral !pgs !v =
  coerceEdhToIntegral' pgs v
    $  throwEdhSTM pgs UsageError
    $  "Integer expected but given a "
    <> T.pack (edhTypeNameOf v)
coerceEdhToIntegral'
  :: (Integral a)
  => EdhProgState
  -> EdhValue
  -> STM ()
  -> (a -> STM ())
  -> STM ()
coerceEdhToIntegral' !pgs !v !naExit !exit = case edhUltimate v of
  EdhDecimal !n -> case D.decimalToInteger n of
    Just !i -> exit $ fromInteger i
    Nothing -> naExit
  EdhObject !o -> lookupEdhObjAttr pgs o (AttrByName "__int__") >>= \case
    EdhNil -> naExit
    EdhMethod !mth ->
      runEdhProc pgs
        $ callEdhMethod o mth (ArgsPack [] mempty) id
        $ \(OriginalValue !rtn _ _) -> case edhUltimate rtn of
            EdhDecimal !n -> contEdhSTM $ case D.decimalToInteger n of
              Just !i -> exit $ fromInteger i
              Nothing ->
                throwEdhSTM pgs EvalError
                  $  "bug: __int__ magin returned non-integer: "
                  <> T.pack (show n)
            !badVal ->
              throwEdh UsageError
                $  "bug: bad value returned from __int__ magic: "
                <> T.pack (edhTypeNameOf badVal)
    !badMagic ->
      throwEdhSTM pgs UsageError $ "Malformed __int__ magic: " <> T.pack
        (edhTypeNameOf badMagic)
  _ -> naExit

