module Dim.EvsDtArts where

-- import           Debug.Trace

import Control.Applicative
import Control.Monad
import Data.Dynamic
import Data.Maybe
import qualified Data.Text as T
import Data.Typeable hiding (typeRep)
import Data.Unique
import Dim.DataType
import Dim.XCHG
import Foreign hiding (void)
import GHC.Float
import Language.Edh.MHI
import System.Random
import Type.Reflection
import Prelude

withThisEvsTyped ::
  forall t r.
  (Typeable t) =>
  (forall s. (EventSource s t) => Object -> s t -> Edh r) ->
  Edh r
withThisEvsTyped withEvs = do
  !this <- edh'scope'this . contextScope . edh'context <$> edhThreadState
  withEventSource this $ \(evs :: s t') -> case eqT of
    Nothing -> throwEdhM EvalError "this EventSource mismatch its dtype"
    Just (Refl :: t' :~: t) -> withEvs this evs

withThisEventSource ::
  forall r.
  (forall s t. (EventSource s t, Typeable t) => Object -> s t -> Edh r) ->
  Edh r
withThisEventSource withEvs = do
  !this <- edh'scope'this . contextScope . edh'context <$> edhThreadState
  withEventSource this $ withEvs this

getEvsDtype :: Object -> Edh Object
getEvsDtype !objEvs = do
  let findEvsDto :: [Object] -> Edh Object
      findEvsDto [] =
        edhSimpleDescM (EdhObject objEvs) >>= \ !badDesc ->
          naM $ "not a Sink/EventSource with dtype: " <> badDesc
      -- this is right and avoids unnecessary checks in vastly usual cases
      findEvsDto [dto] = return dto
      -- safe guard in case an evs instance has been further extended
      findEvsDto (maybeDto : rest) =
        (<|> findEvsDto rest) $
          withDataType maybeDto $ const $ return maybeDto
  readTVarEdh (edh'obj'supers objEvs) >>= findEvsDto

mkYesNoEvtDt :: Object -> DataTypeIdent -> Edh Object
mkYesNoEvtDt clsEvs !dti = do
  !dtCls <- mkEdhClass dti (allocObjM dtypeAllocator) [] $ pure ()
  !idObj <- newUniqueEdh
  !supersVar <- newTVarEdh []
  let !dtYesNo =
        Object
          { edh'obj'ident = idObj,
            edh'obj'store = dtd,
            edh'obj'class = dtCls,
            edh'obj'supers = supersVar
          }
  !clsMths <-
    sequence $
      [ (AttrByName nm,) <$> mkEdhProc vc nm hp
        | (nm, vc, hp) <-
            [ ( "(==)",
                EdhMethod,
                wrapEdhProc $
                  evsCmpProc dtYesNo ((==) :: YesNo -> YesNo -> Bool)
              ),
              ( "(==.)",
                EdhMethod,
                wrapEdhProc $
                  evsCmpProc dtYesNo ((==) :: YesNo -> YesNo -> Bool)
              ),
              ( "(!=)",
                EdhMethod,
                wrapEdhProc $
                  evsCmpProc dtYesNo ((/=) :: YesNo -> YesNo -> Bool)
              ),
              ( "(!=.)",
                EdhMethod,
                wrapEdhProc $
                  evsCmpProc dtYesNo ((/=) :: YesNo -> YesNo -> Bool)
              ),
              ("(&&)", EdhMethod, wrapEdhProc $ evsOpProc @YesNo clsEvs (.&.)),
              ("(&&.)", EdhMethod, wrapEdhProc $ evsOpProc @YesNo clsEvs (.&.)),
              ("(||)", EdhMethod, wrapEdhProc $ evsOpProc @YesNo clsEvs (.|.)),
              ("(||.)", EdhMethod, wrapEdhProc $ evsOpProc @YesNo clsEvs (.|.)),
              ("__eq__", EdhMethod, wrapEdhProc evsDtypeEqProc)
            ]
      ]
  let !clsArts = clsMths ++ [(AttrByName "__repr__", EdhString dti)]
  !clsScope <- inlineSTM $ objectScope dtCls
  iopdUpdateEdh clsArts $ edh'scope'entity clsScope
  return dtYesNo
  where
    !dtd = HostStore $ toDyn dt
    dt :: DataType YesNo
    dt = mkIntDataType @YesNo dti

    dtypeAllocator :: Edh (Maybe Unique, ObjectStore)
    dtypeAllocator = return (Nothing, dtd)

mkFloatEvtDt ::
  forall a.
  Object ->
  (RealFloat a, Random a, Num a, Storable a, EdhXchg a, Typeable a) =>
  Object ->
  DataTypeIdent ->
  Edh Object
mkFloatEvtDt clsEvs !dtYesNo !dti = do
  !dtCls <- mkEdhClass dti (allocObjM dtypeAllocator) [] $ do
    !clsMths <-
      sequence $
        [ (AttrByName nm,) <$> mkEdhProc vc nm hp
          | (nm, vc, hp) <-
              [ ( "(==)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (==)
                ),
                ( "(==.)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (==)
                ),
                ( "(!=)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (/=)
                ),
                ( "(!=.)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (/=)
                ),
                ( "(>=)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (>=)
                ),
                ( "(>=.)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (<=)
                ),
                ( "(<=)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (<=)
                ),
                ( "(<=.)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (>=)
                ),
                ( "(>)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (>)
                ),
                ( "(>.)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (<)
                ),
                ( "(<)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (<)
                ),
                ( "(<.)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (>)
                ),
                ( "(+)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (+)
                ),
                ( "(+.)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (+)
                ),
                ( "(-)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (-)
                ),
                ( "(-.)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (flip (-))
                ),
                ( "(*)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (*)
                ),
                ( "(*.)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (*)
                ),
                ( "(/)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (/)
                ),
                ( "(/.)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (flip (/))
                ),
                -- TODO reason about this:
                -- https://stackoverflow.com/questions/38588815/rounding-errors-in-python-floor-division
                ( "(//)",
                  EdhMethod,
                  wrapEdhProc $
                    evsOpProc @a clsEvs (\ !x !y -> fromInteger $ floor $ x / y)
                ),
                ( "(//.)",
                  EdhMethod,
                  wrapEdhProc $
                    evsOpProc @a clsEvs (\ !x !y -> fromInteger $ floor $ y / x)
                ),
                ( "(**)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (**)
                ),
                ( "(**.)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (flip (**))
                ),
                ("__eq__", EdhMethod, wrapEdhProc evsDtypeEqProc)
              ]
        ]
    let !clsArts = clsMths ++ [(AttrByName "__repr__", EdhString dti)]
    !clsScope <- contextScope . edh'context <$> edhThreadState
    iopdUpdateEdh clsArts $ edh'scope'entity clsScope
  !idObj <- newUniqueEdh
  !supersVar <- newTVarEdh []
  let !dtObj =
        Object
          { edh'obj'ident = idObj,
            edh'obj'store = dtd,
            edh'obj'class = dtCls,
            edh'obj'supers = supersVar
          }
  return dtObj
  where
    !dtd = HostStore $ toDyn dt
    dt :: DataType a
    dt = mkFloatDataType @a dti

    dtypeAllocator :: Edh (Maybe Unique, ObjectStore)
    dtypeAllocator = return (Nothing, dtd)

mkIntEvtDt ::
  forall a.
  Object ->
  (Bits a, Integral a, Random a, Num a, Storable a, EdhXchg a, Typeable a) =>
  Object ->
  DataTypeIdent ->
  Edh Object
mkIntEvtDt clsEvs !dtYesNo !dti = do
  !dtCls <- mkEdhClass dti (allocObjM dtypeAllocator) [] $ do
    !clsMths <-
      sequence $
        [ (AttrByName nm,) <$> mkEdhProc vc nm hp
          | (nm, vc, hp) <-
              [ ( "(==)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (==)
                ),
                ( "(==.)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (==)
                ),
                ( "(!=)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (/=)
                ),
                ( "(!=.)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (/=)
                ),
                ( "(>=)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (>=)
                ),
                ( "(>=.)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (<=)
                ),
                ( "(<=)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (<=)
                ),
                ( "(<=.)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (>=)
                ),
                ( "(>)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (>)
                ),
                ( "(>.)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (<)
                ),
                ( "(<)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (<)
                ),
                ( "(<.)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (>)
                ),
                ( "(+)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (+)
                ),
                ( "(+.)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (+)
                ),
                ( "(-)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (-)
                ),
                ( "(-.)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (flip (-))
                ),
                ( "(*)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (*)
                ),
                ( "(*.)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (*)
                ),
                ( "(/)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs div
                ),
                ( "(/.)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (flip div)
                ),
                ( "(//)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs div
                ),
                ( "(//.)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (flip div)
                ),
                ( "(**)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs intPow
                ),
                ( "(**.)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs $ flip intPow
                ),
                ( "(&&)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (.&.)
                ),
                ( "(&&.)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (.&.)
                ),
                ( "(||)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (.|.)
                ),
                ( "(||.)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (.|.)
                ),
                ("__eq__", EdhMethod, wrapEdhProc evsDtypeEqProc)
              ]
        ]
    let !clsArts = clsMths ++ [(AttrByName "__repr__", EdhString dti)]
    !clsScope <- contextScope . edh'context <$> edhThreadState
    iopdUpdateEdh clsArts $ edh'scope'entity clsScope
  !idObj <- newUniqueEdh
  !supersVar <- newTVarEdh []
  let !dtObj =
        Object
          { edh'obj'ident = idObj,
            edh'obj'store = dtd,
            edh'obj'class = dtCls,
            edh'obj'supers = supersVar
          }
  return dtObj
  where
    !dtd = HostStore $ toDyn dt
    dt :: DataType a
    dt = mkIntDataType @a dti

    dtypeAllocator :: Edh (Maybe Unique, ObjectStore)
    dtypeAllocator = return (Nothing, dtd)

    intPow :: a -> a -> a
    intPow _ 0 = 1
    intPow x y
      -- TODO this justifies?
      | y < 0 = 0 -- to survive `Exception: Negative exponent`
      | otherwise = x ^ y

mkBitsEvtDt ::
  forall a.
  Object ->
  (Bits a, Ord a, Storable a, EdhXchg a, Typeable a) =>
  Object ->
  DataTypeIdent ->
  Edh Object
mkBitsEvtDt clsEvs !dtYesNo !dti = do
  !dtCls <- mkEdhClass dti (allocObjM dtypeAllocator) [] $ do
    !clsMths <-
      sequence $
        [ (AttrByName nm,) <$> mkEdhProc vc nm hp
          | (nm, vc, hp) <-
              [ ( "(==)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (==)
                ),
                ( "(==.)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (==)
                ),
                ( "(!=)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (/=)
                ),
                ( "(!=.)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (/=)
                ),
                ( "(>=)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (>=)
                ),
                ( "(>=.)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (<=)
                ),
                ( "(<=)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (<=)
                ),
                ( "(<=.)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (>=)
                ),
                ( "(>)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (>)
                ),
                ( "(>.)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (<)
                ),
                ( "(<)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (<)
                ),
                ( "(<.)",
                  EdhMethod,
                  wrapEdhProc $ evsCmpProc @a dtYesNo (>)
                ),
                ( "(&&)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (.&.)
                ),
                ( "(&&.)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (.&.)
                ),
                ( "(||)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (.|.)
                ),
                ( "(||.)",
                  EdhMethod,
                  wrapEdhProc $ evsOpProc @a clsEvs (.|.)
                ),
                ("__eq__", EdhMethod, wrapEdhProc evsDtypeEqProc)
              ]
        ]
    let !clsArts = clsMths ++ [(AttrByName "__repr__", EdhString dti)]
    !clsScope <- contextScope . edh'context <$> edhThreadState
    iopdUpdateEdh clsArts $ edh'scope'entity clsScope
  !idObj <- newUniqueEdh
  !supersVar <- newTVarEdh []
  let !dtObj =
        Object
          { edh'obj'ident = idObj,
            edh'obj'store = dtd,
            edh'obj'class = dtCls,
            edh'obj'supers = supersVar
          }
  return dtObj
  where
    !dtd = HostStore $ toDyn dt
    dt :: DataType a
    dt = mkBitsDataType @a dti

    dtypeAllocator :: Edh (Maybe Unique, ObjectStore)
    dtypeAllocator = return (Nothing, dtd)

evsCmpProc ::
  forall a.
  (Eq a, EdhXchg a, Typeable a) =>
  Object ->
  (a -> a -> Bool) ->
  EdhValue ->
  Edh EdhValue
evsCmpProc !dtYesNo !cmp !other =
  withThisEvsTyped @a $ \ !thisEvsObj (thisEvs :: s a) -> do
    let exitWithResult :: MappedEvs s a YesNo -> Edh EdhValue
        exitWithResult !evsResult = do
          EdhObject
            <$> createHostObjectM'
              (edh'obj'class thisEvsObj)
              (toDyn $ SomeEventSource evsResult)
              [dtYesNo]

        withEvs =
          adaptEdhArg @AnyEventSource other
            >>= \(AnyEventSource (otherEvs :: s' t) _otherEvsObj) ->
              case eqT of
                Just (Refl :: t :~: a) -> exitWithResult $
                  MappedEvs thisEvs $ \ !thisEvd ->
                    lingering otherEvs >>= \case
                      Nothing -> return $ yesOrNo False
                      Just !rhv -> return $ yesOrNo $ cmp thisEvd rhv
                Nothing ->
                  throwEdhM UsageError $
                    T.pack $
                      "incompatible event data type: " <> show (typeRep @t)
                        <> " vs "
                        <> show (typeRep @a)

        withValue =
          fromEdh' @a other >>= \case
            Nothing -> return edhNA
            Just !rhv -> exitWithResult $
              MappedEvs thisEvs $ \ !thisEvd ->
                return $ yesOrNo $ cmp thisEvd rhv

    withEvs <|> withValue

evsOpProc ::
  forall a.
  Object ->
  (Eq a, EdhXchg a, Typeable a) =>
  (a -> a -> a) ->
  EdhValue ->
  Edh EdhValue
evsOpProc clsEvs !op !other =
  withThisEvsTyped @a $ \ !thisEvsObj (thisEvs :: s a) -> do
    let exitWithResult :: MappedEvs s a a -> Edh EdhValue
        exitWithResult !evsResult = do
          dto <- getEvsDtype thisEvsObj
          EdhObject
            <$> createHostObjectM'
              clsEvs
              (toDyn $ SomeEventSource evsResult)
              [dto]

        withEvs =
          adaptEdhArg @AnyEventSource other
            >>= \(AnyEventSource (evs :: s' t) _evso) -> case eqT of
              Just (Refl :: t :~: a) -> exitWithResult $
                MappedEvs thisEvs $ \thisEvd ->
                  lingering evs >>= \case
                    Nothing -> return thisEvd -- TODO this okay??
                    Just !rhv -> return $ op thisEvd rhv
              Nothing ->
                throwEdhM UsageError $
                  T.pack $
                    "incompatible event data type: " <> show (typeRep @t)
                      <> " vs "
                      <> show (typeRep @a)

        withValue =
          fromEdh' @a other >>= \case
            Nothing -> return edhNA
            Just !rhv -> exitWithResult $
              MappedEvs thisEvs $ \thisEvd -> return $ op thisEvd rhv

    withEvs <|> withValue

evsDtypeEqProc :: EdhValue -> Edh EdhValue
evsDtypeEqProc !other = do
  !this <- edh'scope'this . contextScope . edh'context <$> edhThreadState
  case edhUltimate other of
    EdhObject !objOther -> (<|> rtnNeg) $
      withDataType objOther $ \ !dtOther ->
        withDataType this $ \ !dtSelf ->
          return $ EdhBool $ isJust $ dtOther `eqDataType` dtSelf
    _ -> rtnNeg
  where
    rtnNeg = return (EdhBool False)
