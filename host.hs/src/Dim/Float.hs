module Dim.Float where

-- import           Debug.Trace

import Control.Applicative
import Control.Monad.IO.Class
import Dim.Column
import Dim.FlatArray
import Dim.InMem
import Event.Analytics.EHI
import Foreign
import Language.Edh.EHI
import Prelude

piProc :: Object -> Object -> Int -> "dtype" ?: Object -> Edh EdhValue
piProc !defaultDt !clsColumn !cap (defaultArg defaultDt -> !dto) =
  (<|> badDtype) $
    withDataType dto $ \case
      DeviceDt (dt :: DeviceDataType a) ->
        (<|> notFloatDt (device'data'type'ident dt)) $
          with'float'device'data'type dt $ do
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
            EdhObject
              <$> createArbiHostObjectM' clsColumn (someColumn col) [dto]
      DirectDt _dt ->
        throwEdhM UsageError "not implemented for direct dtype yet"
      DummyDt _dti ->
        throwEdhM UsageError "not implemented for dummy dtype yet"
  where
    badDtype =
      edhObjDescM dto >>= \ !badDesc ->
        throwEdhM UsageError $ "invalid dtype: " <> badDesc

    notFloatDt dti = throwEdhM UsageError $ "not a floating dtype: " <> dti

floatOpProc ::
  (forall a. Floating a => a -> a) -> "col" !: Object -> Edh EdhValue
floatOpProc !fop (mandatoryArg -> !colObj) =
  getColumnDtype colObj >>= \ !dto -> do
    let badDtype =
          edhObjDescM dto >>= \ !badDesc ->
            throwEdhM UsageError $ "invalid dtype: " <> badDesc
    (<|> badDtype) $
      withDataType dto $ \case
        DeviceDt (dt :: DeviceDataType a) ->
          (<|> notFloatDt (device'data'type'ident dt)) $
            with'float'device'data'type dt $
              (<|> dtMismatch) $
                withColumnOf @a colObj $ \ !colInst !col -> liftEIO $ do
                  (cs, cl) <- view'column'data col
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
                  !csv <- newTMVarEIO cs'
                  !clv <- newTVarEIO cl
                  let !col' = InMemDevCol csv clv
                  liftEdh $
                    EdhObject
                      <$> mutCloneArbiHostObjectM
                        colObj
                        colInst
                        (someColumn col')
        DirectDt _dt ->
          throwEdhM UsageError "not implemented for direct dtype yet"
        DummyDt _dti ->
          throwEdhM UsageError "not implemented for dummy dtype yet"
  where
    notFloatDt dti = throwEdhM UsageError $ "not a floating dtype: " <> dti
    dtMismatch = throwEdhM EvalError "bug: dtype mismatch column"
