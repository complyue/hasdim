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
import Dim.Tensor
import Dim.XCHG
import Foreign hiding (void)
import GHC.Float
import Language.Edh.MHI
import System.Random
import Type.Reflection
import Prelude

mkYesNoEvtDt :: DataTypeIdent -> Edh Object
mkYesNoEvtDt !dti = do
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
                  evtCmpProc dtYesNo ((==) :: YesNo -> YesNo -> Bool)
              ),
              ( "(==.)",
                EdhMethod,
                wrapEdhProc $
                  evtCmpProc dtYesNo ((==) :: YesNo -> YesNo -> Bool)
              ),
              ( "(!=)",
                EdhMethod,
                wrapEdhProc $
                  evtCmpProc dtYesNo ((/=) :: YesNo -> YesNo -> Bool)
              ),
              ( "(!=.)",
                EdhMethod,
                wrapEdhProc $
                  evtCmpProc dtYesNo ((/=) :: YesNo -> YesNo -> Bool)
              ),
              ("(&&)", EdhMethod, wrapEdhProc $ evtOpProc @YesNo (.&.)),
              ("(&&.)", EdhMethod, wrapEdhProc $ evtOpProc @YesNo (.&.)),
              ("(||)", EdhMethod, wrapEdhProc $ evtOpProc @YesNo (.|.)),
              ("(||.)", EdhMethod, wrapEdhProc $ evtOpProc @YesNo (.|.)),
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
  (RealFloat a, Random a, Num a, Storable a, EdhXchg a, Typeable a) =>
  Object ->
  DataTypeIdent ->
  Edh Object
mkFloatEvtDt !dtYesNo !dti = do
  !dtCls <- mkEdhClass dti (allocObjM dtypeAllocator) [] $ do
    !clsMths <-
      sequence $
        [ (AttrByName nm,) <$> mkEdhProc vc nm hp
          | (nm, vc, hp) <-
              [ ( "(==)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (==)
                ),
                ( "(==.)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (==)
                ),
                ( "(!=)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (/=)
                ),
                ( "(!=.)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (/=)
                ),
                ( "(>=)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (>=)
                ),
                ( "(>=.)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (<=)
                ),
                ( "(<=)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (<=)
                ),
                ( "(<=.)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (>=)
                ),
                ( "(>)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (>)
                ),
                ( "(>.)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (<)
                ),
                ( "(<)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (<)
                ),
                ( "(<.)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (>)
                ),
                ( "(+)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (+)
                ),
                ( "(+.)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (+)
                ),
                ( "(-)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (-)
                ),
                ( "(-.)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (flip (-))
                ),
                ( "(*)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (*)
                ),
                ( "(*.)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (*)
                ),
                ( "(/)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (/)
                ),
                ( "(/.)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (flip (/))
                ),
                -- TODO reason about this:
                -- https://stackoverflow.com/questions/38588815/rounding-errors-in-python-floor-division
                ( "(//)",
                  EdhMethod,
                  wrapEdhProc $
                    evtOpProc @a (\ !x !y -> fromInteger $ floor $ x / y)
                ),
                ( "(//.)",
                  EdhMethod,
                  wrapEdhProc $
                    evtOpProc @a (\ !x !y -> fromInteger $ floor $ y / x)
                ),
                ( "(**)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (**)
                ),
                ( "(**.)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (flip (**))
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
  (Bits a, Integral a, Random a, Num a, Storable a, EdhXchg a, Typeable a) =>
  Object ->
  DataTypeIdent ->
  Edh Object
mkIntEvtDt !dtYesNo !dti = do
  !dtCls <- mkEdhClass dti (allocObjM dtypeAllocator) [] $ do
    !clsMths <-
      sequence $
        [ (AttrByName nm,) <$> mkEdhProc vc nm hp
          | (nm, vc, hp) <-
              [ ( "(==)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (==)
                ),
                ( "(==.)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (==)
                ),
                ( "(!=)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (/=)
                ),
                ( "(!=.)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (/=)
                ),
                ( "(>=)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (>=)
                ),
                ( "(>=.)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (<=)
                ),
                ( "(<=)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (<=)
                ),
                ( "(<=.)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (>=)
                ),
                ( "(>)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (>)
                ),
                ( "(>.)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (<)
                ),
                ( "(<)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (<)
                ),
                ( "(<.)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (>)
                ),
                ( "(+)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (+)
                ),
                ( "(+.)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (+)
                ),
                ( "(-)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (-)
                ),
                ( "(-.)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (flip (-))
                ),
                ( "(*)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (*)
                ),
                ( "(*.)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (*)
                ),
                ( "(/)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a div
                ),
                ( "(/.)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (flip div)
                ),
                ( "(//)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a div
                ),
                ( "(//.)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (flip div)
                ),
                ( "(**)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc intPow
                ),
                ( "(**.)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc $ flip intPow
                ),
                ( "(&&)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (.&.)
                ),
                ( "(&&.)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (.&.)
                ),
                ( "(||)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (.|.)
                ),
                ( "(||.)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (.|.)
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
  (Bits a, Ord a, Storable a, EdhXchg a, Typeable a) =>
  Object ->
  DataTypeIdent ->
  Edh Object
mkBitsEvtDt !dtYesNo !dti = do
  !dtCls <- mkEdhClass dti (allocObjM dtypeAllocator) [] $ do
    !clsMths <-
      sequence $
        [ (AttrByName nm,) <$> mkEdhProc vc nm hp
          | (nm, vc, hp) <-
              [ ( "(==)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (==)
                ),
                ( "(==.)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (==)
                ),
                ( "(!=)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (/=)
                ),
                ( "(!=.)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (/=)
                ),
                ( "(>=)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (>=)
                ),
                ( "(>=.)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (<=)
                ),
                ( "(<=)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (<=)
                ),
                ( "(<=.)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (>=)
                ),
                ( "(>)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (>)
                ),
                ( "(>.)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (<)
                ),
                ( "(<)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (<)
                ),
                ( "(<.)",
                  EdhMethod,
                  wrapEdhProc $ evtCmpProc @a dtYesNo (>)
                ),
                ( "(&&)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (.&.)
                ),
                ( "(&&.)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (.&.)
                ),
                ( "(||)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (.|.)
                ),
                ( "(||.)",
                  EdhMethod,
                  wrapEdhProc $ evtOpProc @a (.|.)
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

evtCmpProc ::
  forall a.
  (Eq a, EdhXchg a, Typeable a) =>
  Object ->
  (a -> a -> Bool) ->
  EdhValue ->
  Edh EdhValue
evtCmpProc !dtYesNo !cmp !other =
  withTensorSelfOf @a $ \ !objEvt (EventTensor src perceiver) -> do
    let exitWithResult :: EventTensor YesNo -> Edh EdhValue
        exitWithResult !evtResult = do
          evs <- getTensorSink objEvt
          EdhObject
            <$> createHostObjectM'
              (edh'obj'class objEvt)
              (toDyn evtResult)
              [dtYesNo, evs]

        withEvs =
          adaptEdhArg @AnyEventSource other
            >>= \(AnyEventSource (evs :: s t) _evso) -> case eqT of
              Just (Refl :: t :~: a) -> exitWithResult $
                EventTensor src $ \evd0 ->
                  lingering evs >>= \case
                    Nothing -> return $ yesOrNo False
                    Just !rhv -> do
                      evd <- perceiver evd0
                      return $ yesOrNo $ cmp evd rhv
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
              EventTensor src $ \evd0 -> do
                evd <- perceiver evd0
                return $ yesOrNo $ cmp evd rhv

    withEvs <|> withValue

evtOpProc ::
  forall a.
  (Eq a, EdhXchg a, Typeable a) =>
  (a -> a -> a) ->
  EdhValue ->
  Edh EdhValue
evtOpProc !op !other =
  withTensorSelfOf @a $ \ !objEvt (EventTensor src perceiver) -> do
    let exitWithNewClone :: EventTensor a -> Edh EdhValue
        exitWithNewClone !evtResult =
          EdhObject <$> mutCloneHostObjectM objEvt objEvt evtResult

        withEvs =
          adaptEdhArg @AnyEventSource other
            >>= \(AnyEventSource (evs :: s t) _evso) -> case eqT of
              Just (Refl :: t :~: a) -> exitWithNewClone $
                EventTensor src $ \evd0 ->
                  lingering evs >>= \case
                    Nothing -> perceiver evd0 -- TODO this okay??
                    Just !rhv -> do
                      evd <- perceiver evd0
                      return $ op evd rhv
              Nothing ->
                throwEdhM UsageError $
                  T.pack $
                    "incompatible event data type: " <> show (typeRep @t)
                      <> " vs "
                      <> show (typeRep @a)

        withValue =
          fromEdh' @a other >>= \case
            Nothing -> return edhNA
            Just !rhv -> exitWithNewClone $
              EventTensor src $ \evd0 -> do
                evd <- perceiver evd0
                return $ op evd rhv

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
