module Dim.Fold where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Monad
import Data.Dynamic
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

newtype FoldOp
  = FoldOp
      ( forall r.
        ( forall a. DataType a -> r -> ((a -> a -> a) -> r) -> r
        )
      )

foldOpProc ::
  "fop" !: FoldOp ->
  "colObj" !: Object ->
  EdhHostProc
foldOpProc
  (mandatoryArg -> FoldOp !fop)
  (mandatoryArg -> !colObj)
  !exit
  !ets = getColDtype colObj $
    \ !dto -> withDataType dto badColDt $ \(dt :: DataType a) -> do
      let dtMismatch =
            throwEdhTx UsageError "bug: Column mismatch its dtype"
          naExit =
            throwEdhTx UsageError $
              "operation not applicable to dtype: " <> data'type'ident dt
      runEdhTx ets $
        fop dt naExit $ \ !op ->
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

data FoldlOp b
  = (EdhXchg b, Typeable b) =>
    FoldlOp (forall r a. DataType a -> r -> ((b -> a -> b) -> r) -> r)

foldlOpProc ::
  "fop" !: Object ->
  "start" !: EdhValue ->
  "col" !: Object ->
  EdhHostProc
foldlOpProc
  (mandatoryArg -> !fopObj)
  (mandatoryArg -> !startVal)
  (mandatoryArg -> !colObj)
  !exit
  !ets = case dynamicHostData fopObj of
    Nothing -> badOp
    Just (Dynamic trFOP monotypedFOP) -> case trFOP of
      App trCtor (_ :: TypeRep b) ->
        case trCtor `eqTypeRep` (typeRep @FoldlOp) of
          Nothing -> badOp
          Just HRefl -> case monotypedFOP of
            FoldlOp fop -> getColDtype colObj $ \ !dto ->
              withDataType dto badColDt $ \(dt :: DataType a) -> do
                let naExit =
                      throwEdhTx UsageError $
                        "fold operation not applicable to dtype: "
                          <> data'type'ident dt
                runEdhTx ets $
                  fop dt naExit $ \ !op ->
                    withColumnOf @a colObj dtMismatch $ \_ col ->
                      view'column'data col $ \(cs, cl) ->
                        fromEdh startVal $ \ !start -> edhContIO $ do
                          let go i v
                                | i >= cl =
                                  atomically $ runEdhTx ets $ toEdh @b v exit
                                | otherwise = do
                                  e <- array'reader cs i
                                  go (i + 1) $ op v e
                          go 0 start
      _ -> badOp
    where
      badOp = edhSimpleDesc ets (EdhObject fopObj) $ \ !badDesc ->
        throwEdh ets UsageError $ "bad foldl operation: " <> badDesc
      badColDt = edhValueRepr ets (EdhObject colObj) $ \ !badDesc ->
        throwEdh ets UsageError $ "no dtype from Column: " <> badDesc
      dtMismatch =
        throwEdhTx UsageError "bug: Column mismatch its dtype"

data FoldrOp b
  = (EdhXchg b, Typeable b) =>
    FoldrOp (forall r a. DataType a -> r -> ((a -> b -> b) -> r) -> r)

foldrOpProc ::
  "fop" !: Object ->
  "start" !: EdhValue ->
  "col" !: Object ->
  EdhHostProc
foldrOpProc
  (mandatoryArg -> !fopObj)
  (mandatoryArg -> !startVal)
  (mandatoryArg -> !colObj)
  !exit
  !ets = case dynamicHostData fopObj of
    Nothing -> badOp
    Just (Dynamic trFOP monotypedFOP) -> case trFOP of
      App trCtor (_ :: TypeRep b) ->
        case trCtor `eqTypeRep` (typeRep @FoldrOp) of
          Nothing -> badOp
          Just HRefl -> case monotypedFOP of
            FoldrOp fop -> getColDtype colObj $
              \ !dto -> withDataType dto badColDt $ \(dt :: DataType a) -> do
                let naExit =
                      throwEdhTx UsageError $
                        "fold operation not applicable to dtype: "
                          <> data'type'ident dt
                runEdhTx ets $
                  fop dt naExit $ \ !op ->
                    withColumnOf @a colObj dtMismatch $ \_ col ->
                      view'column'data col $ \(cs, cl) ->
                        fromEdh startVal $ \ !start -> edhContIO $ do
                          let go i v
                                | i < 0 =
                                  atomically $ runEdhTx ets $ toEdh @b v exit
                                | otherwise = do
                                  e <- array'reader cs i
                                  go (i - 1) $ op e v
                          go (cl - 1) start
      _ -> badOp
    where
      badOp = edhSimpleDesc ets (EdhObject fopObj) $ \ !badDesc ->
        throwEdh ets UsageError $ "bad foldl operation: " <> badDesc
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

addOp :: FoldOp
addOp = FoldOp $ \(gdt :: DataType a) naExit exit -> case gdt of
  DeviceDt dt -> device'data'type'as'of'num dt naExit $ \(_ :: TypeRep a) ->
    exit (+)
  DirectDt dt -> direct'data'type'as'of'num dt naExit $ \(_ :: TypeRep a) ->
    exit (+)

addValidOp :: FoldOp
addValidOp = FoldOp $ \(gdt :: DataType a) naExit exit -> case gdt of
  DeviceDt dt -> do
    let usualNum = device'data'type'as'of'num dt naExit $ \(_ :: TypeRep a) ->
          exit (+)
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

mulOp :: FoldOp
mulOp = FoldOp $ \(gdt :: DataType a) naExit exit -> case gdt of
  DeviceDt dt -> device'data'type'as'of'num dt naExit $ \(_ :: TypeRep a) ->
    exit (*)
  DirectDt dt -> direct'data'type'as'of'num dt naExit $ \(_ :: TypeRep a) ->
    exit (*)

mulValidOp :: FoldOp
mulValidOp = FoldOp $ \(gdt :: DataType a) naExit exit -> case gdt of
  DeviceDt dt -> do
    let usualNum = device'data'type'as'of'num dt naExit $ \(_ :: TypeRep a) ->
          exit (*)
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
      exit (*)
