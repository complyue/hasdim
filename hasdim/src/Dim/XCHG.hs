module Dim.XCHG where

import           Prelude
-- import           Debug.Trace

import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import qualified Data.Text                     as T

import           Data.Scientific

import           Data.Lossless.Decimal         as D

import           Language.Edh.EHI


class EdhXchg t where
  toEdh :: EdhProgState -> t -> (EdhValue -> STM ()) -> STM ()
  fromEdh :: EdhProgState  -> EdhValue -> (t -> STM ()) -> STM ()


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
  fromEdh _pgs (EdhDecimal !n) !exit = exit $ fromRational $ toRational n
  fromEdh !pgs !v _ =
    throwEdhSTM pgs EvalError $ "Number expected but given a " <> T.pack
      (edhTypeNameOf v)

instance {-# OVERLAPPABLE #-} EdhXchg Float where
  toEdh _pgs !n !exit =
    exit $ EdhDecimal $ D.decimalFromScientific $ fromFloatDigits n
  fromEdh _pgs (EdhDecimal !n) !exit = exit $ fromRational $ toRational n
  fromEdh !pgs !v _ =
    throwEdhSTM pgs EvalError $ "Number expected but given a " <> T.pack
      (edhTypeNameOf v)

instance {-# OVERLAPPABLE #-} (Integral a) => EdhXchg a where
  toEdh _pgs !n !exit = exit $ EdhDecimal $ fromIntegral n
  fromEdh !pgs (EdhDecimal !n) !exit = case D.decimalToInteger n of
    Nothing ->
      throwEdhSTM pgs EvalError $ "Not an integer: " <> T.pack (show n)
    Just !i -> exit $ fromInteger i
  fromEdh !pgs !v _ =
    throwEdhSTM pgs EvalError $ "Integer expected but given a " <> T.pack
      (edhTypeNameOf v)

