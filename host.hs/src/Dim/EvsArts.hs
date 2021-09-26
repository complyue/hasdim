module Dim.EvsArts where

-- import           Debug.Trace

import Control.Applicative
import Control.Monad
import Data.Dynamic
import Data.Maybe
import qualified Data.Text as T
import Data.Unique
import Dim.DataType
import Dim.EvsDtArts
import Dim.Tensor
import Language.Edh.MHI
import Type.Reflection
import Prelude

defineEvsArts :: Edh [(AttrKey, EdhValue)]
defineEvsArts = do
  dtYesNo <- mkYesNoEvtDt "YesNo"
  dtDouble <- mkFloatEvtDt @Double dtYesNo "Double"
  clsTensor <- createTensorClass
  clsSink <- createSinkClass clsTensor dtDouble
  return
    [ (AttrByName "Sink", EdhObject clsSink),
      (AttrByName "EventTensor", EdhObject clsTensor),
      (AttrByName "Double", EdhObject dtDouble),
      (AttrByName "YesNo", EdhObject dtYesNo)
    ]

createTensorClass :: Edh Object
createTensorClass =
  mkEdhClass "EventTensor" (allocObjM evtAllocator) [] $ do
    mthRepr <- mkEdhProc' EdhMethod "__repr__" evtReprProc
    let mths =
          [ (AttrByName "__repr__", mthRepr)
          ]
    props <-
      sequence
        [ (AttrByName nm,) <$> mkEdhProperty nm getter setter
          | (nm, getter, setter) <- [("sink", getSinkProc, Nothing)]
        ]
    let clsArts = mths ++ props
    !clsScope <- contextScope . edh'context <$> edhThreadState
    iopdUpdateEdh clsArts $ edh'scope'entity clsScope
  where
    evtAllocator :: ArgsPack -> Edh (Maybe Unique, ObjectStore)
    evtAllocator _ =
      throwEdhM UsageError "EventTensor not constructable by script"

    withThisTensor ::
      forall r.
      (forall a. Typeable a => Object -> EventTensor a -> Edh r) ->
      Edh r
    withThisTensor withEvs = do
      !this <- edh'scope'this . contextScope . edh'context <$> edhThreadState
      case dynamicHostData this of
        Nothing -> throwEdhM EvalError "bug: this is not an EventTensor"
        Just (Dynamic trEvs evt) -> case trEvs of
          App trTensor trEvt ->
            case trTensor `eqTypeRep` typeRep @EventTensor of
              Just HRefl -> withTypeable trEvt $ withEvs this evt
              Nothing -> throwEdhM EvalError "bug: this is not an EventTensor"
          _ -> throwEdhM EvalError "bug: this is not an EventTensor"

    evtReprProc :: Edh EdhValue
    evtReprProc = withThisTensor $ \this (_evt :: EventTensor a) -> do
      !dto <- getTensorDtype this
      !dtRepr <- edhObjReprM dto
      let evtRepr = "EventTensor( dtype= " <> dtRepr <> " )"
      return $ EdhString evtRepr

    getSinkProc :: Edh EdhValue
    getSinkProc = do
      !this <- edh'scope'this . contextScope . edh'context <$> edhThreadState
      EdhObject <$> getTensorSink this

createSinkClass :: Object -> Object -> Edh Object
createSinkClass !clsTensor !defaultDt =
  mkEdhClass "Sink" (allocObjM evsAllocator) [] $ do
    mthInit <- mkEdhProc' EdhMethod "__init__" evs__init__
    mthRepr <- mkEdhProc' EdhMethod "__repr__" evsReprProc
    mthShow <- mkEdhProc' EdhMethod "__show__" evsShowProc
    mthPerceive <- mkEdhProc' EdhIntrpr "__perceive__" evsPerceive
    let mths =
          [ (AttrByName "__init__", mthInit),
            (AttrByName "__repr__", mthRepr),
            (AttrByName "__show__", mthShow),
            (AttrByName "__perceive__", mthPerceive)
          ]
    props <-
      sequence
        [ (AttrByName nm,) <$> mkEdhProperty nm getter setter
          | (nm, getter, setter) <- [("dtype", evsDtypeProc, Nothing)]
        ]
    let clsArts = mths ++ props
    !clsScope <- contextScope . edh'context <$> edhThreadState
    iopdUpdateEdh clsArts $ edh'scope'entity clsScope
  where
    evsAllocator ::
      "dtype" ?: Object ->
      ArgsPack -> -- allow/ignore arbitrary ctor args for descendant classes
      Edh (Maybe Unique, ObjectStore)
    evsAllocator (defaultArg defaultDt -> dto) _ctorOtherArgs =
      withDataType dto $ \case
        DeviceDt (_dt :: DeviceDataType a) -> do
          evs <- newEventSinkEdh @a
          return
            ( Nothing,
              HostStore $ toDyn $ SomeEventSink evs
            )
        DirectDt dt -> case direct'data'default dt of
          (_fill'val :: a) -> do
            evs <- newEventSinkEdh @a
            return
              ( Nothing,
                HostStore $ toDyn $ SomeEventSink evs
              )

    evs__init__ ::
      "dtype" ?: Object ->
      ArgsPack -> -- allow/ignore arbitrary ctor args for descendant classes
      Edh EdhValue
    evs__init__ (defaultArg defaultDt -> dto) _ctorOtherArgs = do
      ets <- edhThreadState
      let scope = contextScope $ edh'context ets
          this = edh'scope'this scope
          that = edh'scope'that scope

          extendsDt :: [Object] -> Edh ()
          extendsDt [] = return ()
          extendsDt (o : rest) = do
            modifyTVarEdh' (edh'obj'supers o) (++ [dto])
            if o == this
              then return ()
              else extendsDt rest

      supers <- readTVarEdh $ edh'obj'supers that
      extendsDt $ that : supers
      return nil

    withThisSink ::
      forall r.
      (forall a. Typeable a => Object -> EventSink a -> Edh r) ->
      Edh r
    withThisSink withEvs = do
      !this <- edh'scope'this . contextScope . edh'context <$> edhThreadState
      asSink this (withEvs this)
        <|> throwEdhM EvalError "bug: this is not a Sink"

    evsReprProc :: Edh EdhValue
    evsReprProc = withThisSink $ \this (_evs :: EventSink a) -> do
      !dto <- getSinkDtype this
      !dtRepr <- edhObjReprM dto
      let evsRepr = "Sink( dtype= " <> dtRepr <> " )"
      return $ EdhString evsRepr

    evsShowProc :: Edh EdhValue
    evsShowProc = withThisSink $ \this (_evs :: EventSink a) -> do
      !dto <- getSinkDtype this
      !dtRepr <- edhObjReprM dto
      let evsRepr = "Sink( dtype= " <> dtRepr <> " )"
      return $
        EdhString $ evsRepr <> " {# " <> T.pack (show $ typeRep @a) <> " #}"

    evsPerceive :: "perceiverBody" !: ExprDefi -> Edh EdhValue
    evsPerceive (mandatoryArg -> pBody) =
      withThisSink $ \this (evs :: EventSink t) -> do
        dto <- getSinkDtype this
        eto <-
          createHostObjectM'
            clsTensor
            (toDyn $ EventTensor @t evs return)
            [dto, this]
        caseValueOfM (EdhObject eto) pBody

    evsDtypeProc :: Edh EdhValue
    evsDtypeProc = do
      !this <- edh'scope'this . contextScope . edh'context <$> edhThreadState
      EdhObject <$> getSinkDtype this
