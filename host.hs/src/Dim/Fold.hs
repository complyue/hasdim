module Dim.Fold where

-- import           Debug.Trace

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Data.Dynamic
import qualified Data.Lossless.Decimal as D
import Data.Maybe
import Data.Typeable hiding (TypeRep, typeOf, typeRep)
import Dim.Column
import Dim.DataType
import Dim.XCHG
import Foreign as F
import Language.Edh.MHI
import Type.Reflection
import Prelude

-- * Support of Folding

class Folding f where
  self'fold ::
    forall m r.
    (MonadPlus m) =>
    f ->
    (forall a. DataType a -> ((a -> a -> a) -> m r) -> m r)

  left'fold ::
    forall m r a b.
    (MonadPlus m) =>
    f ->
    DataType a ->
    DataType b ->
    ((b -> a -> b) -> m r) ->
    m r

  right'fold ::
    forall m r a b.
    (MonadPlus m) =>
    f ->
    DataType a ->
    DataType b ->
    ((a -> b -> b) -> m r) ->
    m r
  right'fold f dt'a dt'b act =
    left'fold f dt'a dt'b $ act . flip

data FoldOp = forall f. (Folding f) => FoldOp f

foldComput ::
  "fop" @: HostValue FoldOp ->
  "colObj" @: Object ->
  Edh EdhValue
foldComput
  (appliedArg -> HostValue (FoldOp !fop) _)
  (appliedArg -> !colObj) =
    getColumnDtype colObj >>= \ !dto ->
      withDataType dto $ \(dt :: DataType a) ->
        ( <|>
            throwEdhM
              UsageError
              ("operation not applicable to dtype: " <> data'type'ident dt)
        )
          $ self'fold fop dt $ \ !op ->
            (<|> throwEdhM EvalError "bug: Column mismatch its dtype") $
              withColumnOf @a colObj $ \_ col -> do
                (cs, cl) <- view'column'data col
                if cl < 1
                  then return edhNA
                  else (toEdh =<<) $
                    liftIO $ do
                      let go :: Int -> a -> IO a
                          go i v
                            | i >= cl = return v
                            | otherwise = do
                              e <- array'reader cs i
                              go (i + 1) $ op v e
                      go 1 =<< array'reader cs 0

foldlComput ::
  "fop" @: HostValue FoldOp ->
  "start" @: EdhValue ->
  "colObj" @: Object ->
  Edh EdhValue
foldlComput
  (appliedArg -> HostValue (FoldOp !fop) _)
  (appliedArg -> !startVal)
  (appliedArg -> !colObj) =
    getColumnDtype colObj >>= \ !dto ->
      withDataType dto $ \(dt :: DataType a) ->
        ( <|>
            throwEdhM
              UsageError
              ("operation not applicable to dtype: " <> data'type'ident dt)
        )
          $ left'fold fop dt dt $ \ !op ->
            (<|> throwEdhM EvalError "bug: Column mismatch its dtype") $
              withColumnOf @a colObj $ \_ col -> do
                (cs, cl) <- view'column'data col
                if cl < 1
                  then return edhNA
                  else do
                    start <- fromEdh startVal
                    (toEdh =<<) $
                      liftIO $ do
                        let go i v
                              | i >= cl = return v
                              | otherwise = do
                                e <- array'reader cs i
                                go (i + 1) $ op v e
                        go 0 start

foldrComput ::
  "fop" @: HostValue FoldOp ->
  "start" @: EdhValue ->
  "colObj" @: Object ->
  Edh EdhValue
foldrComput
  (appliedArg -> HostValue (FoldOp !fop) _)
  (appliedArg -> !startVal)
  (appliedArg -> !colObj) =
    getColumnDtype colObj >>= \ !dto ->
      withDataType dto $ \(dt :: DataType a) ->
        ( <|>
            throwEdhM
              UsageError
              ("operation not applicable to dtype: " <> data'type'ident dt)
        )
          $ right'fold fop dt dt $ \ !op ->
            (<|> throwEdhM EvalError "bug: Column mismatch its dtype") $
              withColumnOf @a colObj $ \_ col -> do
                (cs, cl) <- view'column'data col
                if cl < 1
                  then return edhNA
                  else do
                    start <- fromEdh startVal
                    (toEdh =<<) $
                      liftIO $ do
                        let go i v
                              | i < 0 = return v
                              | otherwise = do
                                e <- array'reader cs i
                                go (i - 1) $ op e v
                        go (cl - 1) start

scanlComput ::
  "fop" @: HostValue FoldOp ->
  "start" @: EdhValue ->
  "colObj" @: Object ->
  Edh EdhValue
scanlComput
  (appliedArg -> HostValue (FoldOp !fop) _)
  (appliedArg -> !startVal)
  (appliedArg -> !colObj) =
    getColumnDtype colObj >>= \ !dto ->
      withDataType dto $ \(dt :: DataType a) ->
        ( <|>
            throwEdhM
              UsageError
              ("operation not applicable to dtype: " <> data'type'ident dt)
        )
          $ left'fold fop dt dt $ \ !op ->
            (<|> throwEdhM EvalError "bug: Column mismatch its dtype") $
              withColumnOf @a colObj $ \colInst col -> do
                start <- fromEdh startVal
                !col' <-
                  liftIO $
                    derive'new'column
                      col
                      (\(_cs, cl, _cap) -> cl)
                      ( \(cs, cl) (cs', _cap) -> do
                          let go i v
                                | i >= cl = return cl
                                | otherwise = do
                                  e <- array'reader cs i
                                  let v' = op v e
                                  array'writer cs' i v'
                                  go (i + 1) v'
                          go 0 start
                      )
                EdhObject
                  <$> createHostObjectM'
                    (edh'obj'class colInst)
                    (toDyn col')
                    [dto]

scanrComput ::
  "fop" @: HostValue FoldOp ->
  "start" @: EdhValue ->
  "colObj" @: Object ->
  Edh EdhValue
scanrComput
  (appliedArg -> HostValue (FoldOp !fop) _)
  (appliedArg -> !startVal)
  (appliedArg -> !colObj) =
    getColumnDtype colObj >>= \ !dto ->
      withDataType dto $ \(dt :: DataType a) ->
        ( <|>
            throwEdhM
              UsageError
              ("operation not applicable to dtype: " <> data'type'ident dt)
        )
          $ right'fold fop dt dt $ \ !op ->
            (<|> throwEdhM EvalError "bug: Column mismatch its dtype") $
              withColumnOf @a colObj $ \colInst col -> do
                start <- fromEdh startVal
                !col' <-
                  liftIO $
                    derive'new'column
                      col
                      (\(_cs, cl, _cap) -> cl)
                      ( \(cs, cl) (cs', _cap) -> do
                          let go i v
                                | i >= cl = return cl
                                | otherwise = do
                                  e <- array'reader cs i
                                  let v' = op v e
                                  array'writer cs' i v'
                                  go (i + 1) v'
                          go 0 start
                      )
                EdhObject
                  <$> createHostObjectM'
                    (edh'obj'class colInst)
                    (toDyn col')
                    [dto]

-- * Implemented Folding Operations

data FoldingAdd = FoldingAdd

instance Folding FoldingAdd where
  self'fold _ (gdt :: DataType a) act = case gdt of
    DeviceDt dt -> with'num'device'data'type dt $ \(_ :: TypeRep a) ->
      act (+)
    DirectDt dt -> with'num'direct'data'type dt $ \(_ :: TypeRep a) ->
      act (+)

  left'fold f (gdt'a :: DataType a) (gdt'b :: DataType b) act =
    case gdt'a `eqDataType` gdt'b of
      Just Refl -> self'fold f gdt'a act
      _ -> mzero -- heterogeneous folding not yet supported

data FoldingMul = FoldingMul

instance Folding FoldingMul where
  self'fold _ (gdt :: DataType a) act = case gdt of
    DeviceDt dt -> with'num'device'data'type dt $ \(_ :: TypeRep a) ->
      act (*)
    DirectDt dt -> with'num'direct'data'type dt $ \(_ :: TypeRep a) ->
      act (*)

  left'fold f (gdt'a :: DataType a) (gdt'b :: DataType b) act =
    case gdt'a `eqDataType` gdt'b of
      Just Refl -> self'fold f gdt'a act
      _ -> mzero -- heterogeneous folding not yet supported

data FoldingAddV = FoldingAddV

instance Folding FoldingAddV where
  self'fold _ (gdt :: DataType a) act = case gdt of
    DeviceDt dt -> do
      let usualNum = with'num'device'data'type dt $ \(_ :: TypeRep a) ->
            act (+)
          floatNum = with'float'device'data'type dt $ \(_ :: TypeRep a) ->
            act $ \lhs rhs ->
              if
                  | isNaN lhs -> rhs
                  | isNaN rhs -> lhs
                  | otherwise -> lhs + rhs
      floatNum <|> usualNum
    DirectDt dt -> case eqT of
      Just (Refl :: a :~: D.Decimal) ->
        act $ \lhs rhs ->
          if
              | D.decimalIsNaN lhs -> rhs
              | D.decimalIsNaN rhs -> lhs
              | otherwise -> lhs + rhs
      Nothing -> with'num'direct'data'type dt $ \(_ :: TypeRep a) ->
        act (+)

  left'fold f (gdt'a :: DataType a) (gdt'b :: DataType b) act =
    case gdt'a `eqDataType` gdt'b of
      Just Refl -> self'fold f gdt'a act
      _ -> mzero -- heterogeneous folding not yet supported

data FoldingMulV = FoldingMulV

instance Folding FoldingMulV where
  self'fold _ (gdt :: DataType a) act = case gdt of
    DeviceDt dt -> do
      let usualNum = with'num'device'data'type dt $ \(_ :: TypeRep a) ->
            act (*)
          floatNum = with'float'device'data'type dt $ \(_ :: TypeRep a) ->
            act $ \lhs rhs ->
              if
                  | isNaN lhs -> rhs
                  | isNaN rhs -> lhs
                  | otherwise -> lhs * rhs
      floatNum <|> usualNum
    DirectDt dt -> case eqT of
      Just (Refl :: a :~: D.Decimal) ->
        act $ \lhs rhs ->
          if
              | D.decimalIsNaN lhs -> rhs
              | D.decimalIsNaN rhs -> lhs
              | otherwise -> lhs * rhs
      Nothing -> with'num'direct'data'type dt $ \(_ :: TypeRep a) ->
        act (*)

  left'fold f (gdt'a :: DataType a) (gdt'b :: DataType b) act =
    case gdt'a `eqDataType` gdt'b of
      Just Refl -> self'fold f gdt'a act
      _ -> mzero -- heterogeneous folding not yet supported
