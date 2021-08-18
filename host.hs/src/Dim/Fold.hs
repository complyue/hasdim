module Dim.Fold where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Monad
import qualified Data.Lossless.Decimal as D
import Data.Maybe
import Data.Typeable hiding (TypeRep, typeOf, typeRep)
import Dim.Column
import Dim.DataType
import Dim.XCHG
import Foreign as F
import Language.Edh.EHI
import Type.Reflection
import Prelude

-- * Support of Folding

class Folding f where
  self'fold ::
    f ->
    forall r. (forall a. DataType a -> r -> ((a -> a -> a) -> r) -> r)

  left'fold ::
    f ->
    forall r a b.
    DataType a ->
    DataType b ->
    r ->
    ((b -> a -> b) -> r) ->
    r

  right'fold ::
    f ->
    forall r a b.
    DataType a ->
    DataType b ->
    r ->
    ((a -> b -> b) -> r) ->
    r
  right'fold f dt'a dt'b naExit exit =
    left'fold f dt'a dt'b naExit $ exit . flip

data FoldOp = forall f. (Folding f) => FoldOp f

foldComput ::
  "fop" @: HostValue FoldOp ->
  "colObj" @: Object ->
  ComputEdh_
foldComput
  (appliedArg -> HostValue (FoldOp !fop) _)
  (appliedArg -> !colObj) = ComputEdh_ comput
    where
      comput :: EdhTxExit EdhValue -> EdhTx
      comput !exit !ets = getColDtype colObj $
        \ !dto -> withDataType dto badColDt $ \(dt :: DataType a) -> do
          let dtMismatch =
                throwEdhTx UsageError "bug: Column mismatch its dtype"
              naExit =
                throwEdhTx UsageError $
                  "operation not applicable to dtype: " <> data'type'ident dt
          runEdhTx ets $
            self'fold fop dt naExit $ \ !op ->
              withColumnOf @a colObj dtMismatch $ \_ col ->
                view'column'data col $ \(cs, cl) ->
                  if cl < 1
                    then exitEdhTx exit nil
                    else edhContIO $ do
                      let go :: Int -> a -> IO ()
                          go i v
                            | i >= cl =
                              atomically $ runEdhTx ets $ toEdh @a v exit
                            | otherwise = do
                              e <- array'reader cs i
                              go (i + 1) $ op v e
                      go 1 =<< array'reader cs 0
        where
          badColDt = edhValueRepr ets (EdhObject colObj) $ \ !badDesc ->
            throwEdh ets UsageError $ "no dtype from Column: " <> badDesc

foldlComput ::
  "fop" @: HostValue FoldOp ->
  "start" @: EdhValue ->
  "colObj" @: Object ->
  ComputEdh_
foldlComput
  (appliedArg -> HostValue (FoldOp !fop) _)
  (appliedArg -> !startVal)
  (appliedArg -> !colObj) = ComputEdh_ comput
    where
      comput :: EdhTxExit EdhValue -> EdhTx
      comput !exit !ets = getColDtype colObj $ \ !dto ->
        withDataType dto badColDt $ \(dt :: DataType a) -> do
          let naExit =
                throwEdhTx UsageError $
                  "fold operation not applicable to dtype: "
                    <> data'type'ident dt
          runEdhTx ets $
            left'fold fop dt dt naExit $ \ !op ->
              withColumnOf @a colObj dtMismatch $ \_ col ->
                view'column'data col $ \(cs, cl) ->
                  fromEdh startVal $ \ !start -> edhContIO $ do
                    let go i v
                          | i >= cl =
                            atomically $
                              runEdhTx ets $ toEdh @a v exit
                          | otherwise = do
                            e <- array'reader cs i
                            go (i + 1) $ op v e
                    go 0 start
        where
          badColDt = edhValueRepr ets (EdhObject colObj) $ \ !badDesc ->
            throwEdh ets UsageError $ "no dtype from Column: " <> badDesc
          dtMismatch =
            throwEdhTx UsageError "bug: Column mismatch its dtype"

foldrComput ::
  "fop" @: HostValue FoldOp ->
  "start" @: EdhValue ->
  "colObj" @: Object ->
  ComputEdh_
foldrComput
  (appliedArg -> HostValue (FoldOp !fop) _)
  (appliedArg -> !startVal)
  (appliedArg -> !colObj) = ComputEdh_ comput
    where
      comput :: EdhTxExit EdhValue -> EdhTx
      comput !exit !ets = getColDtype colObj $
        \ !dto ->
          withDataType dto badColDt $ \(dt :: DataType a) -> do
            let naExit =
                  throwEdhTx UsageError $
                    "fold operation not applicable to dtype: "
                      <> data'type'ident dt
            runEdhTx ets $
              right'fold fop dt dt naExit $ \ !op ->
                withColumnOf @a colObj dtMismatch $ \_ col ->
                  view'column'data col $ \(cs, cl) ->
                    fromEdh startVal $ \ !start -> edhContIO $ do
                      let go i v
                            | i < 0 =
                              atomically $
                                runEdhTx ets $ toEdh @a v exit
                            | otherwise = do
                              e <- array'reader cs i
                              go (i - 1) $ op e v
                      go (cl - 1) start
        where
          badColDt = edhValueRepr ets (EdhObject colObj) $ \ !badDesc ->
            throwEdh ets UsageError $ "no dtype from Column: " <> badDesc
          dtMismatch =
            throwEdhTx UsageError "bug: Column mismatch its dtype"

{-

scanOpProc ::
  "col" !: Object ->
  "identityVal" !: EdhValue ->
  "associativeOp" !: (Text -> Dynamic) ->
  EdhHostProc
scanOpProc
  (mandatoryArg -> !colThat)
  (mandatoryArg -> !identVal)
  (mandatoryArg -> !getOp)
  !exit
  !ets = withDerivedHostObject ets colThat $ \ !colThis (Column !col) -> do
    let !dt = data'type'of'column col
        !ident = edhUltimate identVal
        exitWithNewClone !colResult =
          edhCloneHostObj ets colThis colThat colResult $
            \ !newColObj -> exitEdh ets exit $ EdhObject newColObj
    !cs <- view'column'data col
    !cl <- read'column'length col
    resolveDataOperator' ets (data'type'identifier dt) cs naExit $
      \ !dtOp -> do
        let !fa = unsafeSliceFlatArray cs 0 cl
        let !dop = getOp (data'type'identifier dt)
        case fromDynamic dop of
          Just EdhNil -> naExit
          _ -> flat'op'scan dtOp ets fa dop ident $ \ !bifa -> do
            !bicsv <- newTVar bifa
            !biclv <- newTVar cl
            exitWithNewClone $ Column $ InMemColumn dt bicsv biclv
    where
      naExit = exitEdh ets exit edhNA
-}

-- * Implemented Folding Operations

data FoldingAdd = FoldingAdd

instance Folding FoldingAdd where
  self'fold _ (gdt :: DataType a) naExit exit = case gdt of
    DeviceDt dt -> device'data'type'as'of'num dt naExit $ \(_ :: TypeRep a) ->
      exit (+)
    DirectDt dt -> direct'data'type'as'of'num dt naExit $ \(_ :: TypeRep a) ->
      exit (+)

  left'fold f (gdt'a :: DataType a) (gdt'b :: DataType b) naExit exit =
    case gdt'a `eqDataType` gdt'b of
      Just Refl -> self'fold f gdt'a naExit exit
      _ -> naExit -- heterogeneous folding not yet supported

data FoldingMul = FoldingMul

instance Folding FoldingMul where
  self'fold _ (gdt :: DataType a) naExit exit = case gdt of
    DeviceDt dt -> device'data'type'as'of'num dt naExit $ \(_ :: TypeRep a) ->
      exit (*)
    DirectDt dt -> direct'data'type'as'of'num dt naExit $ \(_ :: TypeRep a) ->
      exit (*)

  left'fold f (gdt'a :: DataType a) (gdt'b :: DataType b) naExit exit =
    case gdt'a `eqDataType` gdt'b of
      Just Refl -> self'fold f gdt'a naExit exit
      _ -> naExit -- heterogeneous folding not yet supported

data FoldingAddV = FoldingAddV

instance Folding FoldingAddV where
  self'fold _ (gdt :: DataType a) naExit exit = case gdt of
    DeviceDt dt -> do
      let usualNum = device'data'type'as'of'num dt naExit $
            \(_ :: TypeRep a) -> exit (+)
      device'data'type'as'of'float dt usualNum $ \(_ :: TypeRep a) ->
        exit $ \lhs rhs ->
          if
              | isNaN lhs -> rhs
              | isNaN rhs -> lhs
              | otherwise -> lhs + rhs
    DirectDt dt -> case eqT of
      Just (Refl :: a :~: D.Decimal) ->
        exit $ \lhs rhs ->
          if
              | D.decimalIsNaN lhs -> rhs
              | D.decimalIsNaN rhs -> lhs
              | otherwise -> lhs + rhs
      Nothing -> direct'data'type'as'of'num dt naExit $ \(_ :: TypeRep a) ->
        exit (+)

  left'fold f (gdt'a :: DataType a) (gdt'b :: DataType b) naExit exit =
    case gdt'a `eqDataType` gdt'b of
      Just Refl -> self'fold f gdt'a naExit exit
      _ -> naExit -- heterogeneous folding not yet supported

data FoldingMulV = FoldingMulV

instance Folding FoldingMulV where
  self'fold _ (gdt :: DataType a) naExit exit = case gdt of
    DeviceDt dt -> do
      let usualNum = device'data'type'as'of'num dt naExit $
            \(_ :: TypeRep a) -> exit (*)
      device'data'type'as'of'float dt usualNum $ \(_ :: TypeRep a) ->
        exit $ \lhs rhs ->
          if
              | isNaN lhs -> rhs
              | isNaN rhs -> lhs
              | otherwise -> lhs * rhs
    DirectDt dt -> case eqT of
      Just (Refl :: a :~: D.Decimal) ->
        exit $ \lhs rhs ->
          if
              | D.decimalIsNaN lhs -> rhs
              | D.decimalIsNaN rhs -> lhs
              | otherwise -> lhs * rhs
      Nothing -> direct'data'type'as'of'num dt naExit $ \(_ :: TypeRep a) ->
        exit (*)

  left'fold f (gdt'a :: DataType a) (gdt'b :: DataType b) naExit exit =
    case gdt'a `eqDataType` gdt'b of
      Just Refl -> self'fold f gdt'a naExit exit
      _ -> naExit -- heterogeneous folding not yet supported
