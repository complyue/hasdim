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
import Language.Edh.MHI
import Type.Reflection
import Prelude

defineEvsArts :: Edh [(AttrKey, EdhValue)]
defineEvsArts = do
  clsEventSource <- createEventSourceClass

  dtYesNo <- mkYesNoEvtDt clsEventSource "YesNo"
  dtDouble <- mkFloatEvtDt @Double clsEventSource dtYesNo "Double"

  clsSink <- createSinkClass dtDouble
  return
    [ (AttrByName "Sink", EdhObject clsSink),
      (AttrByName "EventSource", EdhObject clsEventSource),
      (AttrByName "Double", EdhObject dtDouble),
      (AttrByName "YesNo", EdhObject dtYesNo)
    ]

createEventSourceClass :: Edh Object
createEventSourceClass =
  mkEdhClass "EventSource" (allocObjM evtAllocator) [] $ do
    mthRepr <- mkEdhProc' EdhMethod "__repr__" evtReprProc
    let mths =
          [ (AttrByName "__repr__", mthRepr)
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
    evtAllocator :: ArgsPack -> Edh (Maybe Unique, ObjectStore)
    evtAllocator _ =
      throwEdhM UsageError "EventSource not constructable by script"

    evtReprProc :: Edh EdhValue
    evtReprProc = withThisEventSource $ \this (_evs :: s t) -> do
      !dto <- getEvsDtype this
      !dtRepr <- edhObjReprM dto
      let evtRepr = "EventSource( dtype= " <> dtRepr <> " )"
      return $ EdhString evtRepr

withThisEventSource ::
  forall r.
  (forall s t. (EventSource s t, Typeable t) => Object -> s t -> Edh r) ->
  Edh r
withThisEventSource withEvs = do
  !this <- edh'scope'this . contextScope . edh'context <$> edhThreadState
  (<|> throwEdhM EvalError "this is not an EventSource") $
    asEventSource this $ withEvs this

createSinkClass :: Object -> Edh Object
createSinkClass !defaultDt =
  mkEdhClass "Sink" (allocObjM evsAllocator) [] $ do
    mthInit <- mkEdhProc' EdhMethod "__init__" evs__init__
    mthRepr <- mkEdhProc' EdhMethod "__repr__" evsReprProc
    mthShow <- mkEdhProc' EdhMethod "__show__" evsShowProc
    let mths =
          [ (AttrByName "__init__", mthInit),
            (AttrByName "__repr__", mthRepr),
            (AttrByName "__show__", mthShow)
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
      (<|> throwEdhM EvalError "bug: this is not a Sink") $
        case dynamicHostData this of
          Nothing -> naM "not a Sink"
          Just (Dynamic trEvs evs) ->
            case trEvs `eqTypeRep` typeRep @SomeEventSink of
              Just HRefl -> case evs of
                SomeEventSink evs' -> withEvs this evs'
              Nothing -> case trEvs of
                App trSink trEvt ->
                  case trSink `eqTypeRep` typeRep @EventSink of
                    Just HRefl -> withTypeable trEvt $ withEvs this evs
                    Nothing -> naM "not a Sink"
                _ -> naM "not a Sink"

    evsReprProc :: Edh EdhValue
    evsReprProc = withThisSink $ \this (_evs :: EventSink a) -> do
      !dto <- getEvsDtype this
      !dtRepr <- edhObjReprM dto
      let evsRepr = "Sink( dtype= " <> dtRepr <> " )"
      return $ EdhString evsRepr

    evsShowProc :: Edh EdhValue
    evsShowProc = withThisSink $ \this (_evs :: EventSink a) -> do
      !dto <- getEvsDtype this
      !dtRepr <- edhObjReprM dto
      let evsRepr = "Sink( dtype= " <> dtRepr <> " )"
      return $
        EdhString $ evsRepr <> " {# " <> T.pack (show $ typeRep @a) <> " #}"

evsDtypeProc :: Edh EdhValue
evsDtypeProc = do
  !this <- edh'scope'this . contextScope . edh'context <$> edhThreadState
  EdhObject <$> getEvsDtype this
