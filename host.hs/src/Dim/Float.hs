{-# LANGUAGE AllowAmbiguousTypes #-}

module Dim.Float where

-- import           Debug.Trace

import Control.Concurrent.STM (STM, newTVar)
import Data.Dynamic (Dynamic, Typeable, fromDynamic, toDyn)
import Data.Text (Text)
import qualified Data.Text as T
import Dim.Column
import Dim.DataType
import Dim.InMem
import Dim.XCHG
import Foreign as F
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.EHI
import Prelude

data FloatOp where
  FloatOp ::
    { float'new'pi'array :: Int -> (FlatArray -> STM ()) -> STM (),
      float'exp :: Dynamic,
      float'log :: Dynamic,
      float'sqrt :: Dynamic,
      float'sin :: Dynamic,
      float'cos :: Dynamic,
      float'tan :: Dynamic,
      float'asin :: Dynamic,
      float'acos :: Dynamic,
      float'atan :: Dynamic,
      float'sinh :: Dynamic,
      float'cosh :: Dynamic,
      float'tanh :: Dynamic,
      float'asinh :: Dynamic,
      float'acosh :: Dynamic,
      float'atanh :: Dynamic
    } ->
    FloatOp

floatOperations ::
  forall a. (Floating a, EdhXchg a, Typeable a, Storable a) => FloatOp
floatOperations =
  FloatOp
    newPiArray
    exp'op
    log'op
    sqrt'op
    sin'op
    cos'op
    tan'op
    asin'op
    acos'op
    atan'op
    sinh'op
    cosh'op
    tanh'op
    asinh'op
    acosh'op
    atanh'op
  where
    newPiArray !cap !exit = (exit =<<) $
      unsafeIOToSTM $ do
        !p <- callocArray @a cap
        !fp <- newForeignPtr finalizerFree p
        let fillPi :: Int -> IO ()
            fillPi !i | i < 0 = return ()
            fillPi !i = do
              pokeElemOff p i (pi :: a)
              fillPi $ i - 1
        fillPi $ cap - 1
        return $ DeviceArray cap fp

    exp'op = toDyn (exp :: a -> a)
    log'op = toDyn (log :: a -> a)
    sqrt'op = toDyn (sqrt :: a -> a)
    sin'op = toDyn (sin :: a -> a)
    cos'op = toDyn (cos :: a -> a)
    tan'op = toDyn (tan :: a -> a)
    asin'op = toDyn (asin :: a -> a)
    acos'op = toDyn (acos :: a -> a)
    atan'op = toDyn (atan :: a -> a)
    sinh'op = toDyn (sinh :: a -> a)
    cosh'op = toDyn (cosh :: a -> a)
    tanh'op = toDyn (tanh :: a -> a)
    asinh'op = toDyn (asinh :: a -> a)
    acosh'op = toDyn (acosh :: a -> a)
    atanh'op = toDyn (atanh :: a -> a)

resolveFloatDataOperator ::
  EdhThreadState -> DataTypeIdent -> (FloatOp -> STM ()) -> STM ()
resolveFloatDataOperator !ets !dti =
  resolveFloatDataOperator' ets dti $
    throwEdh ets UsageError $
      "operation not supported by dtype: "
        <> dti

resolveFloatDataOperator' ::
  EdhThreadState -> DataTypeIdent -> STM () -> (FloatOp -> STM ()) -> STM ()
resolveFloatDataOperator' !ets !dti !naExit !exit =
  runEdhTx ets $
    performEdhEffect
      (AttrBySym resolveFloatDataOperatorEffId)
      [EdhString dti]
      []
      $ \case
        EdhNil -> const naExit
        EdhObject !dmrpo -> \_ets ->
          castObjectStore dmrpo >>= \case
            Nothing -> naExit
            Just (_, DataManiRoutinePack _dmrp'dti _dmrp'cate !drp) ->
              case fromDynamic drp of
                Nothing ->
                  throwEdh ets UsageError $
                    "bug: data manipulation routine pack obtained for dtype "
                      <> dti
                      <> " is of wrong type: "
                      <> T.pack (show drp)
                Just !rp -> exit rp
        !badDtVal ->
          throwEdhTx UsageError $
            "bad return type from @resolveFloatDataOperator(dti): "
              <> edhTypeNameOf badDtVal

resolveFloatDataOperatorEffId :: Symbol
resolveFloatDataOperatorEffId = globalSymbol "@resolveFloatDataOperator"

-- | The ultimate fallback to have trivial data types resolved
resolveFloatDataOperatorProc :: Object -> "dti" !: Text -> EdhHostProc
resolveFloatDataOperatorProc !dmrpClass (mandatoryArg -> !dti) !exit !ets =
  case dti of
    "float64" -> exitWith (floatOperations @Double)
    "float32" -> exitWith (floatOperations @Float)
    _ ->
      throwEdh ets UsageError $
        "no effective support for such operation on dtype="
          <> dti
          <> ", please find some framework/lib to provide such effectful support"
  where
    exitWith :: FloatOp -> STM ()
    exitWith !drp =
      edhCreateHostObj
        dmrpClass
        (toDyn $ DataManiRoutinePack dti "op" (toDyn drp))
        []
        >>= exitEdh ets exit
          . EdhObject

piProc :: Object -> Object -> Int -> "dtype" ?: Object -> EdhHostProc
piProc !defaultDt !colClass !cap (defaultArg defaultDt -> !dto) !exit !ets =
  castObjectStore dto >>= \case
    Nothing -> throwEdh ets UsageError "invalid dtype"
    Just (_, !dt) ->
      resolveFloatDataOperator ets (data'type'identifier dt) $ \ !fo ->
        float'new'pi'array fo cap $ \ !cs -> do
          !csv <- newTVar cs
          !clv <- newTVar $ flatArrayCapacity cs
          let !col = Column $ InMemColumn dt csv clv
          edhCreateHostObj colClass (toDyn col) []
            >>= exitEdh ets exit
              . EdhObject

floatOpProc :: (FloatOp -> Dynamic) -> "colObj" !: Object -> EdhHostProc
floatOpProc !fop (mandatoryArg -> !colObj) !exit !ets =
  castObjectStore colObj >>= \case
    Nothing -> edhValueDesc ets (EdhObject colObj) $ \ !badDesc ->
      throwEdh ets UsageError $ "not a column object: " <> badDesc
    Just (!thisCol, Column !col) -> do
      let !dt = data'type'of'column col
      !cs <- view'column'data col
      !cl <- read'column'length col
      case cs of
        DeviceArray !cap !fp ->
          resolveFloatDataOperator ets (data'type'identifier dt) $ \ !fo ->
            case fromDynamic $ fop fo of
              Nothing -> throwEdh ets EvalError "bug: float op type mismatch"
              Just (op :: a -> a) -> do
                !rfa <- unsafeIOToSTM $
                  withForeignPtr fp $ \(p :: Ptr a) -> do
                    !rp <- callocArray cap
                    !rfp <- newForeignPtr finalizerFree rp
                    let go i | i >= cap = return $ DeviceArray cap rfp
                        go i = do
                          !ev <- peekElemOff p i
                          pokeElemOff rp i $ op ev
                          go (i + 1)
                    go 0
                !rcsv <- newTVar rfa
                !rclv <- newTVar cl
                edhCloneHostObj
                  ets
                  thisCol
                  colObj
                  (Column $ InMemColumn dt rcsv rclv)
                  $ \ !newColObj -> exitEdh ets exit $ EdhObject newColObj
        _ -> throwEdh ets UsageError "host dtype not supported"
