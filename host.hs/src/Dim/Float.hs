module Dim.Float where

-- import           Debug.Trace

import Control.Concurrent.STM
import Data.Dynamic
import Dim.Column
import Dim.DataType
import Dim.InMem
import Foreign
import Language.Edh.EHI
import Type.Reflection
import Prelude

piProc :: Object -> Object -> Int -> "dtype" ?: Object -> EdhHostProc
piProc !defaultDt !colClass !cap (defaultArg defaultDt -> !dto) !exit !ets =
  withDataType dto badDtype $ \case
    DeviceDt dt -> device'data'type'as'of'float
      dt
      (notFloatDt $ device'data'type'ident dt)
      $ \(_ :: TypeRep a) ->
        runEdhTx ets $
          edhContIO $ do
            !p <- callocArray @a cap
            !fp <- newForeignPtr finalizerFree p
            let fillRng :: Int -> IO ()
                fillRng !i =
                  if i >= cap
                    then return ()
                    else do
                      pokeElemOff p i pi
                      fillRng (i + 1)
            fillRng 0
            atomically $ do
              let !cs = DeviceArray cap fp
              !csv <- newTMVar cs
              !clv <- newTVar cap
              let !col = InMemDevCol csv clv
              edhCreateHostObj'
                colClass
                (toDyn $ someColumn col)
                [dto]
                >>= exitEdh ets exit . EdhObject
    DirectDt _dt ->
      throwEdh ets UsageError "not implemented for direct dtype yet"
  where
    badDtype = edhSimpleDesc ets (EdhObject dto) $ \ !badDesc ->
      throwEdh ets UsageError $ "invalid dtype: " <> badDesc

    notFloatDt dti = throwEdh ets UsageError $ "not a floating dtype: " <> dti

floatOpProc ::
  (forall a. Floating a => a -> a) -> "col" !: Object -> EdhHostProc
floatOpProc !fop (mandatoryArg -> !colObj) !exit !ets =
  getColumnDtype ets colObj $ \ !dto -> runEdhTx ets $ do
    let badDtype = edhSimpleDescTx (EdhObject dto) $ \ !badDesc ->
          throwEdhTx UsageError $ "invalid dtype: " <> badDesc
    withDataType dto badDtype $ \case
      DeviceDt dt -> device'data'type'as'of'float
        dt
        (notFloatDt $ device'data'type'ident dt)
        $ \(_ :: TypeRep a) ->
          withColumnOf @a colObj dtMismatch $ \ !colInst !col ->
            edhContIO $
              view'column'data col $ \(cs, cl) -> do
                !p <- callocArray @a cl
                !fp <- newForeignPtr finalizerFree p
                let pumpAt :: Int -> IO ()
                    pumpAt !i =
                      if i >= cl
                        then return ()
                        else do
                          array'reader cs i >>= pokeElemOff p i . fop
                          pumpAt (i + 1)
                pumpAt 0
                atomically $ do
                  let !cs' = DeviceArray cl fp
                  !csv <- newTMVar cs'
                  !clv <- newTVar cl
                  let !col' = InMemDevCol csv clv
                  edhCloneHostObj ets colInst colObj (someColumn col') $
                    exitEdh ets exit . EdhObject
      DirectDt _dt ->
        throwEdhTx UsageError "not implemented for direct dtype yet"
  where
    notFloatDt dti = throwEdhTx UsageError $ "not a floating dtype: " <> dti
    dtMismatch = throwEdhTx EvalError "bug: dtype mismatch column"
