module Dim.Float where

-- import           Debug.Trace

import Control.Applicative
import Control.Monad.IO.Class
import Data.Dynamic
import Dim.Column
import Dim.DataType
import Dim.InMem
import Foreign
import Language.Edh.EHI
import Type.Reflection
import Prelude

piProc :: Object -> Object -> Int -> "dtype" ?: Object -> Edh EdhValue
piProc !defaultDt !colClass !cap (defaultArg defaultDt -> !dto) =
  (<|> badDtype) $
    withDataType dto $ \case
      DeviceDt dt -> device'data'type'as'of'float
        dt
        (notFloatDt $ device'data'type'ident dt)
        $ \(_ :: TypeRep a) -> do
          !fp <- liftIO $ do
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
            return fp

          let !cs = DeviceArray cap fp
          !csv <- newTMVarEdh cs
          !clv <- newTVarEdh cap
          let !col = InMemDevCol csv clv
          edhCreateHostObj'
            colClass
            (toDyn $ someColumn col)
            [dto]
            >>= exitEdh ets exit . EdhObject
      DirectDt _dt ->
        throwEdhM UsageError "not implemented for direct dtype yet"
  where
    badDtype =
      edhObjDescM dto >>= \ !badDesc ->
        throwEdhM UsageError $ "invalid dtype: " <> badDesc

    notFloatDt dti = throwEdh ets UsageError $ "not a floating dtype: " <> dti

floatOpProc ::
  (forall a. Floating a => a -> a) -> "col" !: Object -> Edh EdhValue
floatOpProc !fop (mandatoryArg -> !colObj) =
  getColumnDtype colObj >>= \ !dto -> do
    let badDtype =
          edhObjDescM dto >>= \ !badDesc ->
            throwEdhM UsageError $ "invalid dtype: " <> badDesc
    (<|> badDtype) $
      withDataType dto $ \case
        DeviceDt dt -> device'data'type'as'of'float
          dt
          (notFloatDt $ device'data'type'ident dt)
          $ \(_ :: TypeRep a) ->
            (<|> dtMismatch) $
              withColumnOf @a colObj $ \ !colInst !col ->
                view'column'data col >>= \(cs, cl) -> do
                  !fp <- liftIO $ do
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
                    return fp

                  let !cs' = DeviceArray cl fp
                  !csv <- newTMVarEdh cs'
                  !clv <- newTVarEdh cl
                  let !col' = InMemDevCol csv clv
                  edhCloneHostObj ets colInst colObj (someColumn col') $
                    exitEdh ets exit . EdhObject
        DirectDt _dt ->
          throwEdhM UsageError "not implemented for direct dtype yet"
  where
    notFloatDt dti = throwEdhM UsageError $ "not a floating dtype: " <> dti
    dtMismatch = throwEdhM EvalError "bug: dtype mismatch column"
