module Dim.Tensor where

-- import           Debug.Trace

import Control.Applicative
import Control.Monad
import Data.Dynamic
import Data.Maybe
import qualified Data.Text as T
import Dim.DataType
import Language.Edh.MHI
import Type.Reflection
import Prelude

data EventTensor t = forall s t0.
  (EventSource s t0) =>
  EventTensor
  { -- | Source of the event tensor
    event'source :: !(s t0),
    -- | Extract the event data as perceived
    event'perceiver :: t0 -> EIO t
  }

asTensorOf ::
  forall a r.
  (Typeable a) =>
  Object ->
  (EventTensor a -> Edh r) ->
  Edh r
asTensorOf !obj !withEvt = case dynamicHostData obj of
  Nothing -> naAct
  Just (Dynamic trEvt evt) -> case trEvt of
    App trEvtC trA -> case trEvtC `eqTypeRep` typeRep @EventTensor of
      Just HRefl -> case trA `eqTypeRep` typeRep @a of
        Just HRefl -> withEvt evt
        _ -> naAct
      _ -> naAct
    _ -> naAct
  where
    naAct =
      naM $ "not expected EventTensor of type: " <> T.pack (show $ typeRep @a)

asTensorOf' ::
  forall a r.
  (Typeable a) =>
  EdhValue ->
  (EventTensor a -> Edh r) ->
  Edh r
asTensorOf' !val !withEvt = case edhUltimate val of
  EdhObject !obj -> asTensorOf obj withEvt
  _ ->
    naM $
      "not expected EventTensor object of type: " <> T.pack (show $ typeRep @a)

withTensorOf ::
  forall a r.
  Typeable a =>
  Object ->
  (Object -> EventTensor a -> Edh r) ->
  Edh r
withTensorOf !obj !withCol = do
  let withComposition :: [Object] -> Edh r
      withComposition [] =
        naM $ "not expected EventTensor of type: " <> T.pack (show $ typeRep @a)
      withComposition (o : rest) =
        (<|> withComposition rest) $
          asTensorOf @a o $ withCol o
  supers <- readTVarEdh $ edh'obj'supers obj
  withComposition $ obj : supers

withTensorOf' ::
  forall a r.
  Typeable a =>
  EdhValue ->
  (Object -> EventTensor a -> Edh r) ->
  Edh r
withTensorOf' !val !withCol = case edhUltimate val of
  EdhObject !obj -> withTensorOf obj withCol
  _ ->
    naM $
      "not expected EventTensor object of type: " <> T.pack (show $ typeRep @a)

withTensorSelfOf ::
  forall a r.
  Typeable a =>
  (Object -> EventTensor a -> Edh r) ->
  Edh r
withTensorSelfOf !withCol = mEdh $ \ !exit !ets -> do
  let that = edh'scope'that $ contextScope $ edh'context ets
  flip (runEdh ets) exit $ withTensorOf @a that withCol

getTensorDtype :: Object -> Edh Object
getTensorDtype !objEvt = do
  let findEvtDto :: [Object] -> Edh Object
      findEvtDto [] =
        edhSimpleDescM (EdhObject objEvt) >>= \ !badDesc ->
          naM $ "not an EventTensor with dtype: " <> badDesc
      findEvtDto (maybeDto : rest) =
        (<|> findEvtDto rest) $ withDataType maybeDto $ const $ return maybeDto
  readTVarEdh (edh'obj'supers objEvt) >>= findEvtDto

getTensorSink :: Object -> Edh Object
getTensorSink !objEvt = do
  let findEvtSo :: [Object] -> Edh Object
      findEvtSo [] =
        edhSimpleDescM (EdhObject objEvt) >>= \ !badDesc ->
          naM $ "not an EventTensor from Sink: " <> badDesc
      -- this is right and avoids unnecessary checks in vastly usual cases
      findEvtSo [sinkObj] = return sinkObj
      -- safe guard in case a EventTensor instance has been further extended
      findEvtSo (maybeSo : rest) =
        (<|> findEvtSo rest) $ asSink maybeSo $ const $ return maybeSo
  readTVarEdh (edh'obj'supers objEvt) >>= findEvtSo

asSink :: Object -> (forall a. Typeable a => EventSink a -> Edh r) -> Edh r
asSink !obj withEvs = case dynamicHostData obj of
  Nothing -> naM "not a Sink"
  Just (Dynamic trEvs evs) -> case trEvs of
    App trSink trEvt -> case trSink `eqTypeRep` typeRep @EventSink of
      Just HRefl -> withTypeable trEvt $ withEvs evs
      Nothing -> naM "not a Sink"
    _ -> naM "not a Sink"

getSinkDtype :: Object -> Edh Object
getSinkDtype !objEvs = do
  let findEvsDto :: [Object] -> Edh Object
      findEvsDto [] =
        edhSimpleDescM (EdhObject objEvs) >>= \ !badDesc ->
          naM $ "not a Sink with dtype: " <> badDesc
      -- this is right and avoids unnecessary checks in vastly usual cases
      findEvsDto [dto] = return dto
      -- safe guard in case a Sink instance has been further extended
      findEvsDto (maybeDto : rest) =
        (<|> findEvsDto rest) $
          withDataType maybeDto $ const $ return maybeDto
  readTVarEdh (edh'obj'supers objEvs) >>= findEvsDto
