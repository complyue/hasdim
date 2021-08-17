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

newtype FoldOp
  = FoldOp
      ( forall r.
        ( forall a. DataType a -> r -> ((a -> a -> a) -> r) -> r
        )
      )

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

{-
newtype SelfFold
  = SelfFold
      ( forall r.
        ((forall a. (Foldee a, Typeable a) => a -> a -> a) -> r) ->
        r
      )

selfFold ::
  (forall a. (Foldee a, Typeable a) => a -> a -> a) -> SelfFold
selfFold !fop = SelfFold $
  \(exit :: forall r. ((forall a. a -> a -> a) -> r)) -> exit (fop @a)

newtype LeftFold
  = LeftFold
      ( forall r.
        ( forall a b.
          (Foldee a, EdhXchg b, Typeable a, Typeable b) =>
          (b -> a -> b) ->
          r
        ) ->
        r
      )

leftFold ::
  (Foldee a, EdhXchg b, Typeable a, Typeable b) =>
  (b -> a -> b) ->
  LeftFold
leftFold !fop = LeftFold ($ fop)

newtype RightFold
  = RightFold
      ( forall r.
        ( forall a b.
          (Foldee a, EdhXchg b, Typeable a, Typeable b) =>
          (a -> b -> b) ->
          r
        ) ->
        r
      )

rightFold ::
  (Foldee a, EdhXchg b, Typeable a, Typeable b) =>
  (a -> b -> b) ->
  RightFold
rightFold !fop = RightFold ($ fop)
-}

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

{-

foldlOpProc ::
  "fop" !: LeftFold ->
  "start" !: EdhValue ->
  "col" !: SomeColumn ->
  EdhHostProc
foldlOpProc
  (mandatoryArg -> !fop)
  (mandatoryArg -> !start)
  (mandatoryArg -> SomeColumn _ !col)
  !exit
  !ets = undefined

foldrOpProc ::
  "fop" !: RightFold ->
  "start" !: EdhValue ->
  "col" !: SomeColumn ->
  EdhHostProc
foldrOpProc
  (mandatoryArg -> !fop)
  (mandatoryArg -> !start)
  (mandatoryArg -> SomeColumn _ !col)
  !exit
  !ets = undefined

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
