module Dim.Fold where

-- import           Debug.Trace

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import qualified Data.Lossless.Decimal as D
import Data.Maybe
import Data.Typeable hiding (TypeRep, typeOf, typeRep)
import Dim.Column
import Dim.FlatArray
import Event.Analytics.EHI
import Foreign as F
import Language.Edh.EHI
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
  "fop" @: HostVal FoldOp ->
  "colObj" @: Object ->
  Edh EdhValue
foldComput
  (appliedArg -> HostVal (FoldOp !fop) _)
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
                (cs, cl) <- liftEIO $ view'column'data col
                if cl < 1
                  then return edhNA
                  else (toEdh =<<) $ do
                    let go :: Int -> a -> IO a
                        go i v
                          | i >= cl = return v
                          | otherwise = do
                            e <- array'reader cs i
                            go (i + 1) $ op v e
                    liftIO $ go 1 =<< array'reader cs 0

foldlComput ::
  "fop" @: HostVal FoldOp ->
  "start" @: EdhValue ->
  "colObj" @: Object ->
  Edh EdhValue
foldlComput
  (appliedArg -> HostVal (FoldOp !fop) _)
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
              withColumnOf @a colObj $ \_ col -> liftEIO $ do
                (cs, cl) <- view'column'data col
                if cl < 1
                  then return edhNA
                  else liftEdh $ do
                    start <- fromEdh startVal
                    (toEdh =<<) $ do
                      let go i v
                            | i >= cl = return v
                            | otherwise = do
                              e <- array'reader cs i
                              go (i + 1) $ op v e
                      liftIO $ go 0 start

foldrComput ::
  "fop" @: HostVal FoldOp ->
  "start" @: EdhValue ->
  "colObj" @: Object ->
  Edh EdhValue
foldrComput
  (appliedArg -> HostVal (FoldOp !fop) _)
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
                (cs, cl) <- liftEIO $ view'column'data col
                if cl < 1
                  then return edhNA
                  else do
                    start <- fromEdh startVal
                    (toEdh =<<) $ do
                      let go i v
                            | i < 0 = return v
                            | otherwise = do
                              e <- array'reader cs i
                              go (i - 1) $ op e v
                      liftIO $ go (cl - 1) start

scanlComput ::
  "fop" @: HostVal FoldOp ->
  "start" @: EdhValue ->
  "colObj" @: Object ->
  Edh EdhValue
scanlComput
  (appliedArg -> HostVal (FoldOp !fop) _)
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
                  liftEIO $
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
                          liftIO $ go 0 start
                      )
                EdhObject
                  <$> createArbiHostObjectM'
                    (edh'obj'class colInst)
                    col'
                    [dto]

scanrComput ::
  "fop" @: HostVal FoldOp ->
  "start" @: EdhValue ->
  "colObj" @: Object ->
  Edh EdhValue
scanrComput
  (appliedArg -> HostVal (FoldOp !fop) _)
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
                  liftEIO $
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
                          liftIO $ go 0 start
                      )
                EdhObject
                  <$> createArbiHostObjectM'
                    (edh'obj'class colInst)
                    col'
                    [dto]

-- * Implemented Folding Operations

data FoldingAdd = FoldingAdd

instance Folding FoldingAdd where
  self'fold _ (gdt :: DataType a) act = case gdt of
    DeviceDt dt -> with'num'device'data'type dt $ act (+)
    DirectDt dt -> with'num'direct'data'type dt $ act (+)
    DummyDt _dti -> mzero

  left'fold f (gdt'a :: DataType a) (gdt'b :: DataType b) act =
    case gdt'a `eqDataType` gdt'b of
      Just Refl -> self'fold f gdt'a act
      _ -> mzero -- heterogeneous folding not yet supported

data FoldingMul = FoldingMul

instance Folding FoldingMul where
  self'fold _ (gdt :: DataType a) act = case gdt of
    DeviceDt dt -> with'num'device'data'type dt $ act (*)
    DirectDt dt -> with'num'direct'data'type dt $ act (*)
    DummyDt _dti -> mzero

  left'fold f (gdt'a :: DataType a) (gdt'b :: DataType b) act =
    case gdt'a `eqDataType` gdt'b of
      Just Refl -> self'fold f gdt'a act
      _ -> mzero -- heterogeneous folding not yet supported

data FoldingAddV = FoldingAddV

instance Folding FoldingAddV where
  self'fold _ (gdt :: DataType a) act = case gdt of
    DeviceDt dt -> do
      let usualNum = with'num'device'data'type dt $ act (+)
          floatNum = with'float'device'data'type dt $
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
      Nothing -> with'num'direct'data'type dt $ act (+)
    DummyDt _dti -> mzero

  left'fold f (gdt'a :: DataType a) (gdt'b :: DataType b) act =
    case gdt'a `eqDataType` gdt'b of
      Just Refl -> self'fold f gdt'a act
      _ -> mzero -- heterogeneous folding not yet supported

data FoldingMulV = FoldingMulV

instance Folding FoldingMulV where
  self'fold _ (gdt :: DataType a) act = case gdt of
    DeviceDt dt -> do
      let usualNum = with'num'device'data'type dt $ act (*)
          floatNum = with'float'device'data'type dt $
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
      Nothing -> with'num'direct'data'type dt $ act (*)
    DummyDt _dti -> mzero

  left'fold f (gdt'a :: DataType a) (gdt'b :: DataType b) act =
    case gdt'a `eqDataType` gdt'b of
      Just Refl -> self'fold f gdt'a act
      _ -> mzero -- heterogeneous folding not yet supported
