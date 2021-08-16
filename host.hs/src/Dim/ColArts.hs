module Dim.ColArts where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Monad
import qualified Data.ByteString.Internal as B
import Data.Dynamic
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as T
import Data.Unique
import qualified Data.Vector.Mutable as MV
import Dim.Column
import Dim.DataType
import Dim.InMem
import Dim.XCHG
import Foreign hiding (void)
import Foreign.ForeignPtr.Unsafe
import GHC.Conc (unsafeIOToSTM)
import GHC.Float
import Language.Edh.EHI
import System.Random
import Type.Reflection
import Prelude

{-

foldOpProc ::
  "col" !: SomeColumn ->
  "identityVal" !: EdhValue ->
  "associativeOp" !: (Text -> Dynamic) ->
  EdhHostProc
foldOpProc
  (mandatoryArg -> SomeColumn !col)
  (mandatoryArg -> !identVal)
  (mandatoryArg -> !getOp)
  !exit
  !ets =
    do
      !cs <- view'column'data col
      !cl <- read'column'length col
      resolveDataOperator' ets (data'type'identifier dt) cs naExit $
        \ !dtOp -> do
          let !fa = unsafeSliceFlatArray cs 0 cl
          let !dop = getOp (data'type'identifier dt)
          case fromDynamic dop of
            Just EdhNil -> naExit
            _ -> flat'op'fold dtOp ets fa dop ident $ exitEdh ets exit
    where
      naExit = exitEdh ets exit edhNA
      !dt = data'type'of'column col
      !ident = edhUltimate identVal

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

mkYesNoSuperDt :: DataTypeIdent -> Scope -> STM Object
mkYesNoSuperDt !dti !outerScope = do
  !dtCls <-
    mkHostClass outerScope dti (allocEdhObj dtypeAllocator) [] $
      const $ return ()
  !idObj <- unsafeIOToSTM newUnique
  !supersVar <- newTVar []
  let !dtYesNo =
        Object
          { edh'obj'ident = idObj,
            edh'obj'store = dtd,
            edh'obj'class = dtCls,
            edh'obj'supers = supersVar
          }
  !clsScope <- objectScope dtCls
  !clsMths <-
    sequence $
      [ (AttrByName nm,) <$> mkHostProc clsScope vc nm hp
        | (nm, vc, hp) <-
            [ ( "(==)",
                EdhMethod,
                wrapHostProc $
                  colCmpProc dtYesNo ((==) :: YesNo -> YesNo -> Bool)
              ),
              ( "(==.)",
                EdhMethod,
                wrapHostProc $
                  colCmpProc dtYesNo ((==) :: YesNo -> YesNo -> Bool)
              ),
              ( "(!=)",
                EdhMethod,
                wrapHostProc $
                  colCmpProc dtYesNo ((/=) :: YesNo -> YesNo -> Bool)
              ),
              ( "(!=.)",
                EdhMethod,
                wrapHostProc $
                  colCmpProc dtYesNo ((/=) :: YesNo -> YesNo -> Bool)
              ),
              ("__eq__", EdhMethod, wrapHostProc dtypeEqProc)
            ]
      ]
  let !clsArts = clsMths ++ [(AttrByName "__repr__", EdhString dti)]
  iopdUpdate clsArts $ edh'scope'entity clsScope
  return dtYesNo
  where
    !dtd = HostStore $ toDyn $ mkIntDataType @YesNo dti

    dtypeAllocator :: EdhObjectAllocator
    dtypeAllocator !ctorExit _ets = ctorExit Nothing dtd

mkBoxSuperDt :: DataTypeIdent -> EdhValue -> Scope -> STM Object
mkBoxSuperDt !dti !defv !outerScope = do
  !dtCls <-
    mkHostClass outerScope dti (allocEdhObj dtypeAllocator) [] $
      const $ return ()
  !idObj <- unsafeIOToSTM newUnique
  !supersVar <- newTVar []
  let !dtBox =
        Object
          { edh'obj'ident = idObj,
            edh'obj'store = dtd,
            edh'obj'class = dtCls,
            edh'obj'supers = supersVar
          }

      evalOp ::
        Bool -> AttrName -> EdhValue -> EdhValue -> EdhTxExit EdhValue -> EdhTx
      evalOp !flipOperands !op lhv rhv exit =
        if flipOperands
          then
            evalInfix
              op
              (LitExpr $ ValueLiteral lhv)
              (LitExpr $ ValueLiteral rhv)
              exit
          else
            evalInfix
              op
              (LitExpr $ ValueLiteral rhv)
              (LitExpr $ ValueLiteral lhv)
              exit

      boxInpProc :: Bool -> AttrName -> EdhValue -> EdhHostProc
      boxInpProc !flipOperands !op !other !exit !ets =
        withColumnSelfOf @EdhValue ets $ \_objCol !col -> do
          let vecOp = runEdhTx ets $
                view'column'data col $ \(cs, cl) -> edhContIO $ do
                  let go i
                        | i < 0 = atomically doExit
                        | otherwise = do
                          lhev <- array'reader cs i
                          atomically $
                            runEdhTx ets $
                              evalOp flipOperands op lhev other $
                                \ !result -> edhContIO $ do
                                  array'writer cs i result
                                  go $ i - 1
                  go $ cl - 1

              elemOp ::
                forall c' f'.
                ManagedColumn c' f' EdhValue =>
                c' EdhValue ->
                STM ()
              elemOp col' = runEdhTx ets $
                view'column'data col $ \(cs, cl) ->
                  view'column'data col' $ \(cs', cl') ->
                    if cl' /= cl
                      then
                        throwEdhTx UsageError $
                          "column length mistmatch: "
                            <> T.pack (show cl)
                            <> " vs "
                            <> T.pack (show cl')
                      else edhContIO $ do
                        let go i
                              | i < 0 = atomically doExit
                              | otherwise = do
                                lhev <- array'reader cs i
                                rhev <- array'reader cs' i
                                atomically $
                                  runEdhTx ets $
                                    evalOp flipOperands op lhev rhev $
                                      \ !result -> edhContIO $ do
                                        array'writer cs i result
                                        go $ i - 1
                        go $ cl - 1

          withColumnOf' @EdhValue other vecOp elemOp
        where
          that = edh'scope'that $ contextScope $ edh'context ets
          doExit = exitEdh ets exit $ EdhObject that

      boxApOpProc :: Bool -> AttrName -> EdhValue -> EdhHostProc
      boxApOpProc !flipOperands !op !other !exit !ets =
        withColumnSelfOf @EdhValue ets $ \ !objCol !col -> do
          let exitWithResult ::
                Typeable (InMemDirCol EdhValue) =>
                InMemDirCol EdhValue ->
                STM ()
              exitWithResult !colResult =
                edhCreateHostObj'
                  (edh'obj'class objCol)
                  (toDyn $ someColumn colResult)
                  [dtBox]
                  >>= exitEdh ets exit . EdhObject

              vecOp = runEdhTx ets $
                view'column'data col $ \(cs, cl) -> edhContIO $ do
                  (iov, csResult) <- newDirectArray @EdhValue edhNA cl
                  let go i
                        | i < 0 = atomically $ do
                          csvResult <- newTMVar csResult
                          clvResult <- newTVar cl
                          exitWithResult $ InMemDirCol csvResult clvResult
                        | otherwise = do
                          lhev <- array'reader cs i
                          atomically $
                            runEdhTx ets $
                              evalOp flipOperands op lhev other $
                                \ !result -> edhContIO $ do
                                  MV.unsafeWrite iov i result
                                  go $ i - 1
                  go $ cl - 1

              elemOp ::
                forall c' f'.
                ManagedColumn c' f' EdhValue =>
                c' EdhValue ->
                STM ()
              elemOp col' = runEdhTx ets $
                view'column'data col $ \(cs, cl) ->
                  view'column'data col' $ \(cs', cl') ->
                    if cl' /= cl
                      then
                        throwEdhTx UsageError $
                          "column length mistmatch: "
                            <> T.pack (show cl)
                            <> " vs "
                            <> T.pack (show cl')
                      else edhContIO $ do
                        (iov, csResult) <- newDirectArray @EdhValue edhNA cl
                        let go i
                              | i < 0 = atomically $ do
                                csvResult <- newTMVar csResult
                                clvResult <- newTVar cl
                                exitWithResult $ InMemDirCol csvResult clvResult
                              | otherwise = do
                                lhev <- array'reader cs i
                                rhev <- array'reader cs' i
                                atomically $
                                  runEdhTx ets $
                                    evalOp flipOperands op lhev rhev $
                                      \ !result -> edhContIO $ do
                                        MV.unsafeWrite iov i result
                                        go $ i - 1
                        go $ cl - 1

          withColumnOf' @EdhValue other vecOp elemOp

  !clsScope <- objectScope dtCls
  !clsMths <-
    sequence $
      [ (AttrByName nm,) <$> mkHostProc clsScope vc nm hp
        | (nm, vc, hp) <-
            [ ("(==)", EdhMethod, wrapHostProc $ boxApOpProc False "=="),
              ("(==.)", EdhMethod, wrapHostProc $ boxApOpProc True "=="),
              ("(!=)", EdhMethod, wrapHostProc $ boxApOpProc False "!="),
              ("(!=.)", EdhMethod, wrapHostProc $ boxApOpProc True "!="),
              ("(>=)", EdhMethod, wrapHostProc $ boxApOpProc False ">="),
              ("(>=.)", EdhMethod, wrapHostProc $ boxApOpProc True ">="),
              ("(<=)", EdhMethod, wrapHostProc $ boxApOpProc False "<="),
              ("(<=.)", EdhMethod, wrapHostProc $ boxApOpProc True "<="),
              ("(>)", EdhMethod, wrapHostProc $ boxApOpProc False ">"),
              ("(>.)", EdhMethod, wrapHostProc $ boxApOpProc True ">"),
              ("(<)", EdhMethod, wrapHostProc $ boxApOpProc False "<"),
              ("(<.)", EdhMethod, wrapHostProc $ boxApOpProc True "<"),
              ("(+)", EdhMethod, wrapHostProc $ boxApOpProc False "+"),
              ("(+.)", EdhMethod, wrapHostProc $ boxApOpProc True "+"),
              ("(-)", EdhMethod, wrapHostProc $ boxApOpProc False "-"),
              ("(-.)", EdhMethod, wrapHostProc $ boxApOpProc True "-"),
              ("(*)", EdhMethod, wrapHostProc $ boxApOpProc False "*"),
              ("(*.)", EdhMethod, wrapHostProc $ boxApOpProc True "*"),
              ("(/)", EdhMethod, wrapHostProc $ boxApOpProc False "/"),
              ("(/.)", EdhMethod, wrapHostProc $ boxApOpProc True "/"),
              ("(//)", EdhMethod, wrapHostProc $ boxApOpProc False "//"),
              ("(//.)", EdhMethod, wrapHostProc $ boxApOpProc True "//"),
              ("(**)", EdhMethod, wrapHostProc $ boxApOpProc False "**"),
              ("(**.)", EdhMethod, wrapHostProc $ boxApOpProc True "**"),
              ("(>=)", EdhMethod, wrapHostProc $ boxApOpProc False ">="),
              ("(>=.)", EdhMethod, wrapHostProc $ boxApOpProc True ">="),
              ("(+=)", EdhMethod, wrapHostProc $ boxInpProc False "+"),
              ("(-=)", EdhMethod, wrapHostProc $ boxInpProc False "-"),
              ("(*=)", EdhMethod, wrapHostProc $ boxInpProc False "*"),
              ("(/=)", EdhMethod, wrapHostProc $ boxInpProc False "/"),
              ("(//=)", EdhMethod, wrapHostProc $ boxInpProc False "//"),
              ("(**=)", EdhMethod, wrapHostProc $ boxInpProc False "**"),
              ("__eq__", EdhMethod, wrapHostProc dtypeEqProc)
            ]
      ]

  let !clsArts = clsMths ++ [(AttrByName "__repr__", EdhString dti)]
  iopdUpdate clsArts $ edh'scope'entity clsScope
  return dtBox
  where
    !dtd = HostStore $ toDyn $ mkBoxDataType dti defv

    dtypeAllocator :: EdhObjectAllocator
    dtypeAllocator !ctorExit _ets = ctorExit Nothing dtd

mkRealFracSuperDt ::
  forall a.
  (RealFrac a, Random a, Eq a, EdhXchg a, Typeable a) =>
  Object ->
  DataTypeIdent ->
  Scope ->
  STM Object
mkRealFracSuperDt !dtYesNo !dti !outerScope = do
  !dtCls <- mkHostClass outerScope dti (allocEdhObj dtypeAllocator) [] $
    \ !clsScope -> do
      !clsMths <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc clsScope vc nm hp
            | (nm, vc, hp) <-
                [ ( "(==)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((==) :: a -> a -> Bool)
                  ),
                  ( "(==.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((==) :: a -> a -> Bool)
                  ),
                  ( "(!=)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((/=) :: a -> a -> Bool)
                  ),
                  ( "(!=.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((/=) :: a -> a -> Bool)
                  ),
                  ( "(>=)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((>=) :: a -> a -> Bool)
                  ),
                  ( "(>=.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((<=) :: a -> a -> Bool)
                  ),
                  ( "(<=)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((<=) :: a -> a -> Bool)
                  ),
                  ( "(<=.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((>=) :: a -> a -> Bool)
                  ),
                  ( "(>)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((>) :: a -> a -> Bool)
                  ),
                  ( "(>.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((<) :: a -> a -> Bool)
                  ),
                  ( "(<)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((<) :: a -> a -> Bool)
                  ),
                  ( "(<.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((>) :: a -> a -> Bool)
                  ),
                  ( "(+)",
                    EdhMethod,
                    wrapHostProc $ dirColOpProc ((+) :: a -> a -> a)
                  ),
                  ( "(+.)",
                    EdhMethod,
                    wrapHostProc $ dirColOpProc ((+) :: a -> a -> a)
                  ),
                  ( "(+=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc ((+) :: a -> a -> a)
                  ),
                  ( "(-)",
                    EdhMethod,
                    wrapHostProc $ dirColOpProc ((-) :: a -> a -> a)
                  ),
                  ( "(-.)",
                    EdhMethod,
                    wrapHostProc $ dirColOpProc (flip (-) :: a -> a -> a)
                  ),
                  ( "(-=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc ((-) :: a -> a -> a)
                  ),
                  ( "(*)",
                    EdhMethod,
                    wrapHostProc $ dirColOpProc ((*) :: a -> a -> a)
                  ),
                  ( "(*.)",
                    EdhMethod,
                    wrapHostProc $ dirColOpProc ((*) :: a -> a -> a)
                  ),
                  ( "(*=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc ((*) :: a -> a -> a)
                  ),
                  ( "(/)",
                    EdhMethod,
                    wrapHostProc $ dirColOpProc ((/) :: a -> a -> a)
                  ),
                  ( "(/.)",
                    EdhMethod,
                    wrapHostProc $ dirColOpProc (flip (/) :: a -> a -> a)
                  ),
                  ( "(/=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc ((/) :: a -> a -> a)
                  ),
                  ( "(//)",
                    EdhMethod,
                    wrapHostProc $
                      dirColOpProc
                        ( (\ !x !y -> fromInteger $ floor $ x / y) ::
                            a -> a -> a
                        )
                  ),
                  ( "(//.)",
                    EdhMethod,
                    wrapHostProc $
                      dirColOpProc
                        ( (\ !x !y -> fromInteger $ floor $ y / x) ::
                            a -> a -> a
                        )
                  ),
                  ( "(//=)",
                    EdhMethod,
                    wrapHostProc $
                      colInpProc
                        ( (\ !x !y -> fromInteger $ floor $ x / y) ::
                            a -> a -> a
                        )
                  ),
                  ( "(**)",
                    EdhMethod,
                    wrapHostProc $ dirColOpProc fracPow
                  ),
                  ( "(**.)",
                    EdhMethod,
                    wrapHostProc $ dirColOpProc $ flip fracPow
                  ),
                  ( "(**=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc fracPow
                  ),
                  ("__eq__", EdhMethod, wrapHostProc dtypeEqProc)
                ]
          ]
      let !clsArts = clsMths ++ [(AttrByName "__repr__", EdhString dti)]
      iopdUpdate clsArts $ edh'scope'entity clsScope
  !idObj <- unsafeIOToSTM newUnique
  !supersVar <- newTVar []
  let !dtObj =
        Object
          { edh'obj'ident = idObj,
            edh'obj'store = dtd,
            edh'obj'class = dtCls,
            edh'obj'supers = supersVar
          }
  return dtObj
  where
    !dtd = HostStore $ toDyn $ mkRealFracDataType @a dti

    dtypeAllocator :: EdhObjectAllocator
    dtypeAllocator !ctorExit _ets = ctorExit Nothing dtd

    fracPow :: a -> a -> a
    fracPow _ 0 = 1
    fracPow x y
      -- TODO this justifies?
      | y < 0 = 0 -- to survive `Exception: Negative exponent`
      | otherwise = x ^ (floor y :: Integer)

mkFloatSuperDt ::
  forall a.
  (RealFloat a, Random a, Num a, Storable a, EdhXchg a, Typeable a) =>
  Object ->
  DataTypeIdent ->
  Scope ->
  STM Object
mkFloatSuperDt !dtYesNo !dti !outerScope = do
  !dtCls <- mkHostClass outerScope dti (allocEdhObj dtypeAllocator) [] $
    \ !clsScope -> do
      !clsMths <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc clsScope vc nm hp
            | (nm, vc, hp) <-
                [ ( "(==)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((==) :: a -> a -> Bool)
                  ),
                  ( "(==.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((==) :: a -> a -> Bool)
                  ),
                  ( "(!=)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((/=) :: a -> a -> Bool)
                  ),
                  ( "(!=.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((/=) :: a -> a -> Bool)
                  ),
                  ( "(>=)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((>=) :: a -> a -> Bool)
                  ),
                  ( "(>=.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((<=) :: a -> a -> Bool)
                  ),
                  ( "(<=)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((<=) :: a -> a -> Bool)
                  ),
                  ( "(<=.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((>=) :: a -> a -> Bool)
                  ),
                  ( "(>)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((>) :: a -> a -> Bool)
                  ),
                  ( "(>.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((<) :: a -> a -> Bool)
                  ),
                  ( "(<)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((<) :: a -> a -> Bool)
                  ),
                  ( "(<.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((>) :: a -> a -> Bool)
                  ),
                  ( "(+)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc ((+) :: a -> a -> a)
                  ),
                  ( "(+.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc ((+) :: a -> a -> a)
                  ),
                  ( "(+=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc ((+) :: a -> a -> a)
                  ),
                  ( "(-)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc ((-) :: a -> a -> a)
                  ),
                  ( "(-.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc (flip (-) :: a -> a -> a)
                  ),
                  ( "(-=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc ((-) :: a -> a -> a)
                  ),
                  ( "(*)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc ((*) :: a -> a -> a)
                  ),
                  ( "(*.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc ((*) :: a -> a -> a)
                  ),
                  ( "(*=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc ((*) :: a -> a -> a)
                  ),
                  ( "(/)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc ((/) :: a -> a -> a)
                  ),
                  ( "(/.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc (flip (/) :: a -> a -> a)
                  ),
                  ( "(/=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc ((/) :: a -> a -> a)
                  ),
                  -- TODO reason about this:
                  -- https://stackoverflow.com/questions/38588815/rounding-errors-in-python-floor-division
                  ( "(//)",
                    EdhMethod,
                    wrapHostProc $
                      dirColOpProc
                        ( (\ !x !y -> fromInteger $ floor $ x / y) ::
                            a -> a -> a
                        )
                  ),
                  ( "(//.)",
                    EdhMethod,
                    wrapHostProc $
                      dirColOpProc
                        ( (\ !x !y -> fromInteger $ floor $ y / x) ::
                            a -> a -> a
                        )
                  ),
                  ( "(//=)",
                    EdhMethod,
                    wrapHostProc $
                      colInpProc
                        ( (\ !x !y -> fromInteger $ floor $ x / y) ::
                            a -> a -> a
                        )
                  ),
                  ( "(**)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc ((**) :: a -> a -> a)
                  ),
                  ( "(**.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc (flip (**) :: a -> a -> a)
                  ),
                  ( "(**=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc ((**) :: a -> a -> a)
                  ),
                  ("__eq__", EdhMethod, wrapHostProc dtypeEqProc)
                ]
          ]
      let !clsArts = clsMths ++ [(AttrByName "__repr__", EdhString dti)]
      iopdUpdate clsArts $ edh'scope'entity clsScope
  !idObj <- unsafeIOToSTM newUnique
  !supersVar <- newTVar []
  let !dtObj =
        Object
          { edh'obj'ident = idObj,
            edh'obj'store = dtd,
            edh'obj'class = dtCls,
            edh'obj'supers = supersVar
          }
  return dtObj
  where
    !dtd = HostStore $ toDyn $ mkFloatDataType @a dti

    dtypeAllocator :: EdhObjectAllocator
    dtypeAllocator !ctorExit _ets = ctorExit Nothing dtd

mkIntSuperDt ::
  forall a.
  (Bits a, Integral a, Random a, Num a, Storable a, EdhXchg a, Typeable a) =>
  Object ->
  DataTypeIdent ->
  Scope ->
  STM Object
mkIntSuperDt !dtYesNo !dti !outerScope = do
  !dtCls <- mkHostClass outerScope dti (allocEdhObj dtypeAllocator) [] $
    \ !clsScope -> do
      !clsMths <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc clsScope vc nm hp
            | (nm, vc, hp) <-
                [ ( "(==)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((==) :: a -> a -> Bool)
                  ),
                  ( "(==.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((==) :: a -> a -> Bool)
                  ),
                  ( "(!=)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((/=) :: a -> a -> Bool)
                  ),
                  ( "(!=.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((/=) :: a -> a -> Bool)
                  ),
                  ( "(>=)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((>=) :: a -> a -> Bool)
                  ),
                  ( "(>=.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((<=) :: a -> a -> Bool)
                  ),
                  ( "(<=)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((<=) :: a -> a -> Bool)
                  ),
                  ( "(<=.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((>=) :: a -> a -> Bool)
                  ),
                  ( "(>)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((>) :: a -> a -> Bool)
                  ),
                  ( "(>.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((<) :: a -> a -> Bool)
                  ),
                  ( "(<)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((<) :: a -> a -> Bool)
                  ),
                  ( "(<.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc dtYesNo ((>) :: a -> a -> Bool)
                  ),
                  ( "(+)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc ((+) :: a -> a -> a)
                  ),
                  ( "(+.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc ((+) :: a -> a -> a)
                  ),
                  ( "(+=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc ((+) :: a -> a -> a)
                  ),
                  ( "(-)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc ((-) :: a -> a -> a)
                  ),
                  ( "(-.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc (flip (-) :: a -> a -> a)
                  ),
                  ( "(-=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc ((-) :: a -> a -> a)
                  ),
                  ( "(*)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc ((*) :: a -> a -> a)
                  ),
                  ( "(*.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc ((*) :: a -> a -> a)
                  ),
                  ( "(*=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc ((*) :: a -> a -> a)
                  ),
                  ( "(/)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc (div :: a -> a -> a)
                  ),
                  ( "(/.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc (flip div :: a -> a -> a)
                  ),
                  ( "(/=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc (div :: a -> a -> a)
                  ),
                  ( "(//)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc (div :: a -> a -> a)
                  ),
                  ( "(//.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc (flip div :: a -> a -> a)
                  ),
                  ( "(//=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc (div :: a -> a -> a)
                  ),
                  ( "(**)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc intPow
                  ),
                  ( "(**.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc $ flip intPow
                  ),
                  ( "(**=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc intPow
                  ),
                  ( "(&&)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc ((.&.) :: a -> a -> a)
                  ),
                  ( "(&&.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc ((.&.) :: a -> a -> a)
                  ),
                  ( "(||)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc ((.|.) :: a -> a -> a)
                  ),
                  ( "(||.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc ((.|.) :: a -> a -> a)
                  ),
                  ( "(&&=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc ((.&.) :: a -> a -> a)
                  ),
                  ( "(||=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc ((.|.) :: a -> a -> a)
                  ),
                  ("__eq__", EdhMethod, wrapHostProc dtypeEqProc)
                ]
          ]
      let !clsArts = clsMths ++ [(AttrByName "__repr__", EdhString dti)]
      iopdUpdate clsArts $ edh'scope'entity clsScope
  !idObj <- unsafeIOToSTM newUnique
  !supersVar <- newTVar []
  let !dtObj =
        Object
          { edh'obj'ident = idObj,
            edh'obj'store = dtd,
            edh'obj'class = dtCls,
            edh'obj'supers = supersVar
          }
  return dtObj
  where
    !dtd = HostStore $ toDyn $ mkIntDataType @a dti

    dtypeAllocator :: EdhObjectAllocator
    dtypeAllocator !ctorExit _ets = ctorExit Nothing dtd

    intPow :: a -> a -> a
    intPow _ 0 = 1
    intPow x y
      -- TODO this justifies?
      | y < 0 = 0 -- to survive `Exception: Negative exponent`
      | otherwise = x ^ y

colCmpProc ::
  forall a.
  (Eq a, EdhXchg a, Typeable a) =>
  Object ->
  (a -> a -> Bool) ->
  EdhValue ->
  EdhHostProc
colCmpProc !dtYesNo !cmp !other !exit !ets =
  withColumnSelfOf @a ets $ \ !objCol !col -> do
    let exitWithResult ::
          Typeable (InMemDevCol YesNo) => InMemDevCol YesNo -> STM ()
        exitWithResult !colResult =
          edhCreateHostObj'
            (edh'obj'class objCol)
            (toDyn $ someColumn colResult)
            [dtYesNo]
            >>= exitEdh ets exit . EdhObject

        vecOp = runEdhTx ets $
          view'column'data col $ \(cs, cl) ->
            fromEdh' @a other naExit $ \rhv -> edhContIO $ do
              (fp, csResult) <- newDeviceArray @YesNo cl
              let p = unsafeForeignPtrToPtr fp
                  go i
                    | i < 0 = return ()
                    | otherwise = do
                      lhev <- array'reader cs i
                      pokeElemOff p i $ yesOrNo $ cmp lhev rhv
                      go $ i - 1
              go $ cl - 1
              atomically $ do
                csvResult <- newTMVar csResult
                clvResult <- newTVar cl
                exitWithResult $ InMemDevCol csvResult clvResult

        elemOp :: forall c' f'. ManagedColumn c' f' a => c' a -> STM ()
        elemOp col' = runEdhTx ets $
          view'column'data col $ \(cs, cl) ->
            view'column'data col' $ \(cs', cl') ->
              if cl' /= cl
                then
                  throwEdhTx UsageError $
                    "column length mistmatch: "
                      <> T.pack (show cl)
                      <> " vs "
                      <> T.pack (show cl')
                else edhContIO $ do
                  (fp, csResult) <- newDeviceArray @YesNo cl
                  let p = unsafeForeignPtrToPtr fp
                      go i
                        | i < 0 = return ()
                        | otherwise = do
                          lhev <- array'reader cs i
                          rhev <- array'reader cs' i
                          pokeElemOff p i $ yesOrNo $ cmp lhev rhev
                          go $ i - 1
                  go $ cl - 1
                  atomically $ do
                    csvResult <- newTMVar csResult
                    clvResult <- newTVar cl
                    exitWithResult $ InMemDevCol csvResult clvResult

    withColumnOf' @a other vecOp elemOp
  where
    naExit = exitEdhTx exit edhNA

devColOpProc ::
  forall a.
  (Storable a, Eq a, EdhXchg a, Typeable a) =>
  (a -> a -> a) ->
  EdhValue ->
  EdhHostProc
devColOpProc !op !other !exit !ets =
  withColumnSelfOf @a ets $ \ !objCol !col -> do
    let exitWithNewClone ::
          forall c' f'.
          (ManagedColumn c' f' a, Typeable (c' a)) =>
          c' a ->
          STM ()
        exitWithNewClone !colResult =
          edhCloneHostObj ets objCol objCol (someColumn colResult) $
            \ !newObj -> exitEdh ets exit $ EdhObject newObj

        vecOp = runEdhTx ets $
          view'column'data col $ \(cs, cl) ->
            fromEdh' @a other naExit $ \rhv -> edhContIO $ do
              (fp, csResult) <- newDeviceArray @a cl
              let p = unsafeForeignPtrToPtr fp
                  go i
                    | i < 0 = return ()
                    | otherwise = do
                      lhev <- array'reader cs i
                      pokeElemOff p i $ op lhev rhv
                      go $ i - 1
              go $ cl - 1
              atomically $ do
                csvResult <- newTMVar csResult
                clvResult <- newTVar cl
                exitWithNewClone $ InMemDevCol csvResult clvResult

        elemOp :: forall c' f'. ManagedColumn c' f' a => c' a -> STM ()
        elemOp col' = runEdhTx ets $
          view'column'data col $ \(cs, cl) ->
            view'column'data col' $ \(cs', cl') ->
              if cl' /= cl
                then
                  throwEdhTx UsageError $
                    "column length mistmatch: "
                      <> T.pack (show cl)
                      <> " vs "
                      <> T.pack (show cl')
                else edhContIO $ do
                  (fp, csResult) <- newDeviceArray @a cl
                  let p = unsafeForeignPtrToPtr fp
                      go i
                        | i < 0 = return ()
                        | otherwise = do
                          lhev <- array'reader cs i
                          rhev <- array'reader cs' i
                          pokeElemOff p i $ op lhev rhev
                          go $ i - 1
                  go $ cl - 1
                  atomically $ do
                    csvResult <- newTMVar csResult
                    clvResult <- newTVar cl
                    exitWithNewClone $ InMemDevCol csvResult clvResult

    withColumnOf' @a other vecOp elemOp
  where
    naExit = exitEdhTx exit edhNA

dirColOpProc ::
  forall a.
  (Eq a, EdhXchg a, Typeable a) =>
  (a -> a -> a) ->
  EdhValue ->
  EdhHostProc
dirColOpProc !op !other !exit !ets =
  withColumnSelfOf @a ets $ \ !objCol !col -> do
    let exitWithNewClone ::
          forall c' f'.
          (ManagedColumn c' f' a, Typeable (c' a)) =>
          c' a ->
          STM ()
        exitWithNewClone !colResult =
          edhCloneHostObj ets objCol objCol (someColumn colResult) $
            \ !newObj -> exitEdh ets exit $ EdhObject newObj

        vecOp = runEdhTx ets $
          view'column'data col $ \(cs, cl) ->
            fromEdh' @a other naExit $ \rhv -> edhContIO $ do
              (iov, csResult) <- newDirectArray @a undefined cl
              let go i
                    | i < 0 = return ()
                    | otherwise = do
                      lhev <- array'reader cs i
                      MV.unsafeWrite iov i $ op lhev rhv
                      go $ i - 1
              go $ cl - 1
              atomically $ do
                csvResult <- newTMVar csResult
                clvResult <- newTVar cl
                exitWithNewClone $ InMemDirCol csvResult clvResult

        elemOp :: forall c' f'. ManagedColumn c' f' a => c' a -> STM ()
        elemOp col' = runEdhTx ets $
          view'column'data col $ \(cs, cl) ->
            view'column'data col' $ \(cs', cl') ->
              if cl' /= cl
                then
                  throwEdhTx UsageError $
                    "column length mistmatch: "
                      <> T.pack (show cl)
                      <> " vs "
                      <> T.pack (show cl')
                else edhContIO $ do
                  (iov, csResult) <- newDirectArray @a undefined cl
                  let go i
                        | i < 0 = return ()
                        | otherwise = do
                          lhev <- array'reader cs i
                          rhev <- array'reader cs' i
                          MV.unsafeWrite iov i $ op lhev rhev
                          go $ i - 1
                  go $ cl - 1
                  atomically $ do
                    csvResult <- newTMVar csResult
                    clvResult <- newTVar cl
                    exitWithNewClone $ InMemDirCol csvResult clvResult

    withColumnOf' @a other vecOp elemOp
  where
    naExit = exitEdhTx exit edhNA

colInpProc ::
  forall a.
  (Eq a, EdhXchg a, Typeable a) =>
  (a -> a -> a) ->
  EdhValue ->
  EdhHostProc
colInpProc !op !other !exit !ets =
  withColumnSelfOf @a ets $ \_objCol !col -> do
    let vecOp = runEdhTx ets $
          view'column'data col $ \(cs, cl) ->
            fromEdh' @a other naExit $ \rhv -> edhContIO $ do
              let go i
                    | i < 0 = return ()
                    | otherwise = do
                      lhev <- array'reader cs i
                      array'writer cs i $ op lhev rhv
                      go $ i - 1
              go $ cl - 1
              atomically doExit

        elemOp :: forall c' f'. ManagedColumn c' f' a => c' a -> STM ()
        elemOp col' = runEdhTx ets $
          view'column'data col $ \(cs, cl) ->
            view'column'data col' $ \(cs', cl') ->
              if cl' /= cl
                then
                  throwEdhTx UsageError $
                    "column length mistmatch: "
                      <> T.pack (show cl)
                      <> " vs "
                      <> T.pack (show cl')
                else edhContIO $ do
                  let go i
                        | i < 0 = return ()
                        | otherwise = do
                          lhev <- array'reader cs i
                          rhev <- array'reader cs' i
                          array'writer cs i $ op lhev rhev
                          go $ i - 1
                  go $ cl - 1
                  atomically doExit

    withColumnOf' @a other vecOp elemOp
  where
    that = edh'scope'that $ contextScope $ edh'context ets
    doExit = exitEdh ets exit $ EdhObject that
    naExit = exitEdhTx exit edhNA

createColumnClass :: Object -> Scope -> STM Object
createColumnClass !defaultDt !clsOuterScope =
  mkHostClass clsOuterScope "Column" (allocEdhObj columnAllocator) [] $
    \ !clsScope -> do
      !mths <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc clsScope vc nm hp
            | (nm, vc, hp) <-
                [ ("__init__", EdhMethod, wrapHostProc col__init__),
                  ("__cap__", EdhMethod, wrapHostProc colCapProc),
                  ("__len__", EdhMethod, wrapHostProc colLenProc),
                  ("__grow__", EdhMethod, wrapHostProc colGrowProc),
                  ("__mark__", EdhMethod, wrapHostProc colMarkLenProc),
                  ("__blob__", EdhMethod, wrapHostProc colBlobProc),
                  ("__json__", EdhMethod, wrapHostProc colJsonProc),
                  ("__repr__", EdhMethod, wrapHostProc colReprProc),
                  ("__show__", EdhMethod, wrapHostProc colShowProc),
                  ("__desc__", EdhMethod, wrapHostProc colDescProc),
                  ("([])", EdhMethod, wrapHostProc colIdxReadProc),
                  ("([=])", EdhMethod, wrapHostProc colIdxWriteProc),
                  {- -- TODO impl. following by super dtypes
                  ("([++=])", EdhMethod, wrapHostProc $ colIdxUpdWithOpProc "++"),
                  ("([+=])", EdhMethod, wrapHostProc $ colIdxUpdWithOpProc "+"),
                  ("([-=])", EdhMethod, wrapHostProc $ colIdxUpdWithOpProc "-"),
                  ("([*=])", EdhMethod, wrapHostProc $ colIdxUpdWithOpProc "*"),
                  ("([/=])", EdhMethod, wrapHostProc $ colIdxUpdWithOpProc "/"),
                  ("([//=])", EdhMethod, wrapHostProc $ colIdxUpdWithOpProc "//"),
                  ("([%=])", EdhMethod, wrapHostProc $ colIdxUpdWithOpProc "%"),
                  ("([**=])", EdhMethod, wrapHostProc $ colIdxUpdWithOpProc "**"),
                  ("([&&=])", EdhMethod, wrapHostProc $ colIdxUpdWithOpProc "&&"),
                  ("([||=])", EdhMethod, wrapHostProc $ colIdxUpdWithOpProc "||"),
                  -}
                  ("copy", EdhMethod, wrapHostProc colCopyProc)
                ]
          ]
            ++ [ (AttrByName nm,) <$> mkHostProperty clsScope nm getter setter
                 | (nm, getter, setter) <- [("dtype", colDtypeProc, Nothing)]
               ]
      iopdUpdate mths $ edh'scope'entity clsScope
  where
    columnAllocator ::
      "capacity" !: Int ->
      "length" ?: Int ->
      "dtype" ?: Object ->
      ArgsPack -> -- allow/ignore arbitrary ctor args for descendant classes
      EdhObjectAllocator
    columnAllocator
      (mandatoryArg -> !ctorCap)
      (defaultArg ctorCap -> !ctorLen)
      (defaultArg defaultDt -> dto)
      _ctorOtherArgs
      !ctorExit
      !etsCtor
        | ctorCap < 0 =
          throwEdh etsCtor UsageError $
            "column capacity should be a positive interger, not "
              <> T.pack (show ctorCap)
        | ctorLen < 0 =
          throwEdh etsCtor UsageError $
            "column length should be zero or a positive integer, not "
              <> T.pack (show ctorLen)
        | otherwise = withDataType dto badDtype devDataCol dirDataCol
        where
          devDataCol :: DeviceDataType -> STM ()
          devDataCol (DeviceDataType _dti dth _ _) =
            dth $ \(_ :: TypeRep a) -> runEdhTx etsCtor $
              edhContIO $ do
                (_fp, !cs) <- newDeviceArray @a ctorCap
                atomically $ do
                  !csv <- newTMVar cs
                  !clv <- newTVar ctorLen
                  ctorExit Nothing $
                    HostStore $
                      toDyn $
                        SomeColumn (typeRep @DeviceArray) $
                          InMemDevCol @a csv clv

          dirDataCol :: DirectDataType -> STM ()
          dirDataCol (DirectDataType _dti dvh _ _) =
            dvh $ \(fill'val :: a) -> runEdhTx etsCtor $
              edhContIO $ do
                (_iov, !cs) <- newDirectArray @a fill'val ctorCap
                atomically $ do
                  !csv <- newTMVar cs
                  !clv <- newTVar ctorLen
                  ctorExit Nothing $
                    HostStore $
                      toDyn $
                        SomeColumn (typeRep @DirectArray) $
                          InMemDirCol @a csv clv

          badDtype = throwEdh etsCtor UsageError "invalid dtype"

    col__init__ ::
      "capacity" !: Int ->
      "length" ?: Int ->
      "dtype" ?: Object ->
      ArgsPack -> -- allow/ignore arbitrary ctor args for descendant classes
      EdhHostProc
    col__init__
      _cap
      _len
      (defaultArg defaultDt -> dto)
      _ctorOtherArgs
      !exit
      !ets = do
        supers <- readTVar $ edh'obj'supers that
        extendsDt $ that : supers
        exitEdh ets exit nil
        where
          scope = contextScope $ edh'context ets
          this = edh'scope'this scope
          that = edh'scope'that scope

          extendsDt :: [Object] -> STM ()
          extendsDt [] = return ()
          extendsDt (o : rest) = do
            modifyTVar' (edh'obj'supers o) (++ [dto])
            if o == this
              then return ()
              else extendsDt rest

    colCapProc :: EdhHostProc
    colCapProc !exit !ets = withColumnSelf ets $ \_objCol !col ->
      runEdhTx ets $
        view'column'data col $ \(cs, _cl) ->
          exitEdhTx exit $ EdhDecimal $ fromIntegral $ array'capacity cs

    colLenProc :: EdhHostProc
    colLenProc !exit !ets = withColumnSelf ets $ \_objCol !col ->
      runEdhTx ets $
        read'column'length col $ \ !len ->
          exitEdhTx exit $ EdhDecimal $ fromIntegral len

    colGrowProc :: "newCap" !: Int -> EdhHostProc
    colGrowProc (mandatoryArg -> !newCap) !exit !ets =
      if newCap < 0
        then
          throwEdh ets UsageError $
            "invalid newCap: " <> T.pack (show newCap)
        else withColumnSelf ets $ \_objCol !col ->
          runEdhTx ets $
            grow'column'capacity col newCap $
              const $
                exitEdhTx exit $
                  EdhObject $ edh'scope'that $ contextScope $ edh'context ets

    colMarkLenProc :: "newLen" !: Int -> EdhHostProc
    colMarkLenProc (mandatoryArg -> !newLen) !exit !ets =
      withColumnSelf ets $ \_objCol !col ->
        runEdhTx ets $
          mark'column'length col newLen $
            const $
              exitEdhTx exit $
                EdhObject $ edh'scope'that $ contextScope $ edh'context ets

    colBlobProc :: EdhHostProc
    colBlobProc !exit !ets = getColDtype this $ \ !dto ->
      withDeviceDataType dto naExit $ \(_ :: TypeRep a) ->
        withStorableColumnSelfOf @a ets $ \_objCol !col -> runEdhTx ets $
          view'column'data col $ \(DeviceArray _cap !fp, !cl) ->
            exitEdhTx exit $
              EdhBlob $
                B.fromForeignPtr
                  (castForeignPtr fp)
                  0
                  (cl * sizeOf (undefined :: a))
      where
        scope = contextScope $ edh'context ets
        this = edh'scope'this scope
        naExit = exitEdh ets exit edhNA

    colJsonProc :: EdhHostProc
    colJsonProc !exit !ets = withColumnSelf ets $ \_objCol !col ->
      runEdhTx ets $
        view'column'data col $ \(!cs, !cl) ->
          if cl < 1
            then exitEdhTx exit $ EdhString "[]"
            else edhContIO $ do
              let go :: Int -> [Text] -> IO ()
                  go !i !elemJsonStrs
                    | i < 0 =
                      atomically $
                        exitEdh ets exit $
                          EdhString $
                            "[" <> T.intercalate "," elemJsonStrs <> "]"
                    | otherwise =
                      array'reader cs i >>= \ !ev -> atomically $
                        runEdhTx ets $
                          toEdh ev $ \ !elemVal ->
                            edhValueJsonTx elemVal $ \ !elemJsonStr ->
                              edhContIO $
                                go (i -1) $ elemJsonStr : elemJsonStrs
              go (cl - 1) []

    colReprProc :: EdhHostProc
    colReprProc !exit !ets = withColumnSelf ets $ \ !objCol !col ->
      getColDtype objCol $ \ !dto -> edhValueRepr ets (EdhObject dto) $
        \ !dtRepr -> runEdhTx ets $
          view'column'data col $ \(!cs, !cl) -> do
            let colRepr =
                  "Column( capacity= "
                    <> T.pack (show $ array'capacity cs)
                    <> ", length= "
                    <> T.pack (show cl)
                    <> ", dtype= "
                    <> dtRepr
                    <> " )"
            exitEdhTx exit $ EdhString colRepr

    colShowProc :: EdhHostProc
    colShowProc !exit !ets = withColumnSelf ets $ \ !objCol !col ->
      getColDtype objCol $ \ !dto -> edhValueRepr ets (EdhObject dto) $
        \ !dtRepr -> runEdhTx ets $
          view'column'data col $ \(!cs, !cl) -> do
            let colRepr =
                  "Column( capacity= "
                    <> T.pack (show $ array'capacity cs)
                    <> ", length= "
                    <> T.pack (show cl)
                    <> ", dtype= "
                    <> dtRepr
                    <> " )"
                exitWithDetails :: Text -> STM ()
                exitWithDetails !details =
                  exitEdh ets exit $ EdhString $ colRepr <> "\n" <> details

                go :: Int -> [Text] -> Int -> Text -> IO ()
                -- TODO don't generate all lines for large columns
                go !i !cumLines !lineIdx !line
                  | i >= cl =
                    atomically $
                      exitWithDetails $
                        if T.null line && null cumLines
                          then "Zero-Length Column"
                          else
                            if null cumLines
                              then line
                              else
                                let !fullLines =
                                      line :
                                      " # " -- todo make this tunable ?
                                        <> T.pack (show lineIdx)
                                        <> " ~ "
                                        <> T.pack (show $ i - 1) :
                                      cumLines
                                    !lineCnt = length fullLines
                                 in if lineCnt > 20
                                      then
                                        T.unlines $
                                          reverse $
                                            take 10 fullLines
                                              ++ ["# ... "] -- todo make this tunable
                                              ++ drop (lineCnt - 10) fullLines
                                      else T.unlines $ reverse fullLines
                go !i !cumLines !lineIdx !line =
                  array'reader cs i >>= \ !ev -> atomically $
                    runEdhTx ets $
                      toEdh ev $ \ !elemVal ->
                        edhValueReprTx elemVal $ \ !elemRepr ->
                          let !tentLine = line <> elemRepr <> ", "
                           in edhContIO $
                                if T.length tentLine > 79 -- todo make this tunable ?
                                  then
                                    go
                                      (i + 1)
                                      ( line :
                                        ( " # " -- todo make this tunable ?
                                            <> T.pack (show lineIdx)
                                            <> " ~ "
                                            <> T.pack (show $ i - 1)
                                        ) :
                                        cumLines
                                      )
                                      i
                                      (elemRepr <> ", ")
                                  else go (i + 1) cumLines lineIdx tentLine
            edhContIO $ go 0 [] 0 ""

    -- TODO impl. this following:
    --      https://pandas.pydata.org/pandas-docs/stable/reference/api/pandas.Series.describe.html
    colDescProc :: EdhHostProc
    colDescProc !exit =
      exitEdhTx exit $
        EdhString $
          " * Statistical Description of Column data,\n"
            <> "   like pandas describe(), is yet to be implemented."

    colIdxReadProc :: EdhValue -> EdhHostProc
    colIdxReadProc !idxVal !exit !ets =
      withColumnSelf ets $ \ !objCol !col -> do
        let withBoolIdx ::
              forall c f. ManagedColumn c f YesNo => c YesNo -> STM ()
            withBoolIdx !idxCol = runEdhTx ets $
              extractColumnBool objCol col idxCol $ \(!newColObj, _newCol) ->
                exitEdhTx exit $ EdhObject newColObj

            withIntpIdx :: forall c f. ManagedColumn c f Int => c Int -> STM ()
            withIntpIdx !idxCol = runEdhTx ets $
              extractColumnFancy objCol col idxCol $ \(!newColObj, _newCol) ->
                exitEdhTx exit $ EdhObject newColObj

            withEdhIdx :: STM ()
            withEdhIdx = parseEdhIndex ets idxVal $ \case
              Left !err -> throwEdh ets UsageError err
              Right !idx -> runEdhTx ets $
                view'column'data col $
                  \(!cs, !cl) -> case idx of
                    EdhIndex !i ->
                      edhContIO $
                        array'reader cs i >>= \ !ev ->
                          atomically $
                            runEdhTx ets $
                              toEdh ev $ \ !elemVal ->
                                exitEdhTx exit elemVal
                    EdhAny -> exitEdhTx exit $ EdhObject that
                    EdhAll -> exitEdhTx exit $ EdhObject that
                    EdhSlice !start !stop !step -> \_ets ->
                      edhRegulateSlice ets cl (start, stop, step) $
                        \(!iStart, !iStop, !iStep) ->
                          runEdhTx ets $
                            sliceColumn objCol col iStart iStop iStep $
                              \(!newColObj, _newCol) ->
                                exitEdhTx exit $ EdhObject newColObj

        withColumnOf' @YesNo
          idxVal
          (withColumnOf' @Int idxVal withEdhIdx withIntpIdx)
          withBoolIdx
      where
        that = edh'scope'that $ contextScope $ edh'context ets

    colIdxWriteProc :: EdhValue -> EdhValue -> EdhHostProc
    colIdxWriteProc !idxVal !other !exit !ets =
      withColumnSelf ets $ \_objCol (col :: _c a) -> runEdhTx ets $
        view'column'data col $ \(!cs, !cl) -> do
          let withScalarRHS :: EdhTx
              withScalarRHS = fromEdh @a other $ \ !rhv -> do
                let byBoolIdx ::
                      forall c f. ManagedColumn c f YesNo => c YesNo -> EdhTx
                    byBoolIdx !idxCol =
                      view'column'data idxCol $ \(idxa, idxl) ->
                        if idxl /= cl
                          then
                            throwEdhTx UsageError $
                              "bool index shape mismatch - "
                                <> T.pack (show idxl)
                                <> " vs "
                                <> T.pack (show cl)
                          else edhContIO $ do
                            let go :: Int -> IO ()
                                go i
                                  | i >= idxl = return ()
                                  | otherwise = do
                                    YesNo yn <- array'reader idxa i
                                    when (yn /= 0) $ array'writer cs i rhv
                                    go (i + 1)
                            go 0
                            atomically $ runEdhTx ets doneAssign

                    byIntpIdx ::
                      forall c f. ManagedColumn c f Int => c Int -> EdhTx
                    byIntpIdx !idxCol = view'column'data idxCol $
                      \(idxa, idxl) -> edhContIO $ do
                        let go :: Int -> IO ()
                            go i
                              | i >= idxl = return ()
                              | otherwise = do
                                idxi <- array'reader idxa i
                                array'writer cs idxi rhv
                                go (i + 1)
                        go 0
                        atomically $ runEdhTx ets doneAssign

                    byEdhIdx :: EdhTx
                    byEdhIdx _ets = parseEdhIndex ets idxVal $ \case
                      Left !err -> throwEdh ets UsageError err
                      Right !idx -> runEdhTx ets $ do
                        let fillAll :: EdhTx
                            fillAll = edhContIO $ do
                              let go :: Int -> IO ()
                                  go i
                                    | i >= cl = return ()
                                    | otherwise = do
                                      array'writer cs i rhv
                                      go (i + 1)
                              go 0
                              atomically $ runEdhTx ets doneAssign
                        case idx of
                          EdhIndex !i -> edhContIO $ do
                            array'writer cs i rhv
                            atomically $ runEdhTx ets doneAssign
                          EdhAny -> fillAll
                          EdhAll -> fillAll
                          EdhSlice !start !stop !step -> \_ets ->
                            edhRegulateSlice ets cl (start, stop, step) $
                              \(!iStart, !iStop, !iStep) -> runEdhTx ets $
                                edhContIO $ do
                                  let go :: Int -> IO ()
                                      go i
                                        | i >= iStop = return ()
                                        | otherwise = do
                                          array'writer cs i rhv
                                          go (i + iStep)
                                  go iStart
                                  atomically $ runEdhTx ets doneAssign

                withColumnOf' @YesNo
                  idxVal
                  (withColumnOf' @Int idxVal byEdhIdx byIntpIdx)
                  byBoolIdx

          withColumnOf' @a other withScalarRHS $ \ !rhsCol ->
            view'column'data rhsCol $ \(cs'rhs, cl'rhs) -> do
              let byBoolIdx ::
                    forall c f. ManagedColumn c f YesNo => c YesNo -> EdhTx
                  byBoolIdx !idxCol =
                    if cl'rhs /= cl
                      then
                        throwEdhTx UsageError $
                          "rhs column shape mismatch - "
                            <> T.pack (show cl'rhs)
                            <> " vs "
                            <> T.pack (show cl)
                      else view'column'data idxCol $ \(idxa, idxl) ->
                        if idxl /= cl
                          then
                            throwEdhTx UsageError $
                              "bool index shape mismatch - "
                                <> T.pack (show idxl)
                                <> " vs "
                                <> T.pack (show cl)
                          else edhContIO $ do
                            let go :: Int -> IO ()
                                go i
                                  | i >= idxl = return ()
                                  | otherwise = do
                                    YesNo yn <- array'reader idxa i
                                    when (yn /= 0) $
                                      array'reader cs'rhs i
                                        >>= array'writer cs i
                                    go (i + 1)
                            go 0
                            atomically $ runEdhTx ets doneAssign

                  byIntpIdx ::
                    forall c f. ManagedColumn c f Int => c Int -> EdhTx
                  byIntpIdx !idxCol = view'column'data idxCol $ \(idxa, idxl) ->
                    if cl'rhs /= idxl
                      then
                        throwEdhTx UsageError $
                          "rhs column shape mismatch fancy index - "
                            <> T.pack (show cl'rhs)
                            <> " vs "
                            <> T.pack (show idxl)
                      else edhContIO $ do
                        let go :: Int -> IO ()
                            go i
                              | i >= idxl = return ()
                              | otherwise = do
                                idxi <- array'reader idxa i
                                array'reader cs'rhs i
                                  >>= array'writer cs idxi
                                go (i + 1)
                        go 0
                        atomically $ runEdhTx ets doneAssign

                  byEdhIdx :: EdhTx
                  byEdhIdx _ets = parseEdhIndex ets idxVal $ \case
                    Left !err -> throwEdh ets UsageError err
                    Right !idx -> runEdhTx ets $ case idx of
                      EdhIndex _i ->
                        throwEdhTx
                          UsageError
                          "can not index-assign a rhs column by scalar index"
                      EdhAny ->
                        throwEdhTx
                          UsageError
                          "can not index-assign a rhs column by Any index"
                      EdhAll ->
                        if cl'rhs /= cl
                          then
                            throwEdhTx UsageError $
                              "rhs column shape mismatch - "
                                <> T.pack (show cl'rhs)
                                <> " vs "
                                <> T.pack (show cl)
                          else edhContIO $ do
                            let go :: Int -> IO ()
                                go i
                                  | i >= cl = return ()
                                  | otherwise = do
                                    array'reader cs'rhs i
                                      >>= array'writer cs i
                                    go (i + 1)
                            go 0
                            atomically $ runEdhTx ets doneAssign
                      EdhSlice !start !stop !step -> \_ets ->
                        edhRegulateSlice ets cl (start, stop, step) $
                          \(!iStart, !iStop, !iStep) ->
                            if cl'rhs < ((iStop - iStart) `quot` iStep)
                              then
                                throwEdh ets UsageError $
                                  "rhs column shape mismatch slicing index - "
                                    <> T.pack (show cl'rhs)
                                    <> " vs "
                                    <> T.pack
                                      ( show iStart <> ":" <> show iStop <> ":"
                                          <> show iStep
                                      )
                              else runEdhTx ets $
                                edhContIO $ do
                                  let go :: Int -> Int -> IO ()
                                      go i n
                                        | i >= iStop = return ()
                                        | otherwise = do
                                          array'reader cs'rhs n
                                            >>= array'writer cs i
                                          go (i + iStep) (n + 1)
                                  go 0 0
                                  atomically $ runEdhTx ets doneAssign

              withColumnOf' @YesNo
                idxVal
                (withColumnOf' @Int idxVal byEdhIdx byIntpIdx)
                byBoolIdx
      where
        doneAssign = exitEdhTx exit other

    colCopyProc :: EdhHostProc
    colCopyProc !exit !ets = withColumnSelf ets $ \ !objCol !col ->
      runEdhTx ets $
        read'column'length col $ \ !cl ->
          copy'column'slice col 0 cl 1 $ \(disp, col') _ets -> case disp of
            StayComposed ->
              edhCloneHostObj ets objCol objCol (someColumn col') $
                \ !newColObj -> exitEdh ets exit $ EdhObject newColObj
            ExtractAlone -> getColDtype objCol $ \ !dto ->
              edhCreateHostObj'
                (edh'obj'class objCol)
                (toDyn $ someColumn col')
                [dto]
                >>= \ !newColObj -> exitEdh ets exit $ EdhObject newColObj

    colDtypeProc :: EdhHostProc
    colDtypeProc !exit !ets = getColDtype this $ exitEdh ets exit . EdhObject
      where
        scope = contextScope $ edh'context ets
        this = edh'scope'this scope

arangeProc ::
  Object ->
  Object ->
  "rangeSpec" !: EdhValue ->
  "dtype" ?: Object ->
  EdhHostProc
arangeProc
  !defaultDt
  !colClass
  (mandatoryArg -> !rngSpec)
  (defaultArg defaultDt -> !dto)
  !exit
  !ets = parseEdhIndex ets (edhUltimate rngSpec) $ \case
    Right (EdhIndex !stop)
      | stop >= 0 -> createRangeCol 0 stop 1
    Right (EdhSlice !start (Just !stopN) !step) -> do
      let !startN = fromMaybe 0 start
      createRangeCol startN stopN $
        fromMaybe (if stopN >= startN then 1 else -1) step
    Left !err -> edhSimpleDesc ets rngSpec $ \ !rngDesc ->
      throwEdh ets UsageError $ "invalid range " <> rngDesc <> " - " <> err
    _ -> edhSimpleDesc ets rngSpec $ \ !rngDesc ->
      throwEdh ets UsageError $ "invalid range " <> rngDesc
    where
      badDtype = edhSimpleDesc ets (EdhObject dto) $ \ !badDesc ->
        throwEdh ets UsageError $ "invalid dtype: " <> badDesc

      notNumDt dti = throwEdh ets UsageError $ "not a numeric dtype: " <> dti

      createRangeCol :: Int -> Int -> Int -> STM ()
      createRangeCol !start !stop !step =
        if (stop > start && step <= 0) || (stop < start && step >= 0)
          then throwEdh ets UsageError "range is not converging"
          else do
            let (q, r) = quotRem (stop - start) step
                !len = if r == 0 then abs q else 1 + abs q
                createDevCol :: DeviceDataType -> STM ()
                createDevCol !dt = device'data'type'as'of'num
                  dt
                  (notNumDt $ device'data'type'ident dt)
                  $ \(_ :: TypeRep a) -> runEdhTx ets $
                    edhContIO $ do
                      !p <- callocArray @a len
                      !fp <- newForeignPtr finalizerFree p
                      let fillRng :: Int -> Int -> IO ()
                          fillRng !n !i =
                            if i >= len
                              then return ()
                              else do
                                pokeElemOff p i $ fromIntegral n
                                fillRng (n + step) (i + 1)
                      fillRng start 0
                      atomically $ do
                        let !cs = DeviceArray len fp
                        !csv <- newTMVar cs
                        !clv <- newTVar len
                        let !col = InMemDevCol csv clv
                        edhCreateHostObj'
                          colClass
                          (toDyn $ someColumn col)
                          [dto]
                          >>= exitEdh ets exit . EdhObject

                createDirCol :: DirectDataType -> STM ()
                createDirCol !dt = direct'data'type'as'of'num
                  dt
                  (notNumDt $ direct'data'type'ident dt)
                  $ \(_ :: TypeRep a) -> runEdhTx ets $
                    edhContIO $ do
                      (iov :: MV.IOVector a) <- MV.new len
                      let fillRng :: Int -> Int -> IO ()
                          fillRng !n !i =
                            if i >= len
                              then return ()
                              else do
                                MV.unsafeWrite iov i $ fromIntegral n
                                fillRng (n + step) (i + 1)
                      fillRng start 0
                      atomically $ do
                        let !cs = DirectArray iov
                        !csv <- newTMVar cs
                        !clv <- newTVar len
                        let !col = InMemDirCol csv clv
                        edhCreateHostObj'
                          colClass
                          (toDyn $ someColumn col)
                          [dto]
                          >>= exitEdh ets exit . EdhObject

            withDataType dto badDtype createDevCol createDirCol

randomProc ::
  Object ->
  Object ->
  "size" !: Int ->
  "rangeSpec" ?: EdhValue ->
  "dtype" ?: Object ->
  EdhHostProc
randomProc
  !defaultDt
  !colClass
  (mandatoryArg -> !size)
  (defaultArg (EdhDecimal 1) -> !rngSpec)
  (defaultArg defaultDt -> !dto)
  !exit
  !ets = case edhUltimate rngSpec of
    EdhRange !lower !upper ->
      createRandomCol (edhBoundValue lower) (edhBoundValue upper)
    _ -> parseEdhIndex ets (edhUltimate rngSpec) $ \case
      Right (EdhIndex !stop) ->
        createRandomCol (EdhDecimal 0) (EdhDecimal $ fromIntegral stop)
      Right (EdhSlice !start (Just !stopN) Nothing) ->
        createRandomCol
          (EdhDecimal $ fromIntegral $ fromMaybe 0 start)
          (EdhDecimal $ fromIntegral stopN)
      Left !err -> edhValueDesc ets rngSpec $ \ !rngDesc ->
        throwEdh ets UsageError $
          "invalid random range " <> rngDesc <> " - " <> err
      _ -> edhValueDesc ets rngSpec $ \ !rngDesc ->
        throwEdh ets UsageError $
          "invalid random range " <> rngDesc
    where
      badDtype = edhSimpleDesc ets (EdhObject dto) $ \ !badDesc ->
        throwEdh ets UsageError $ "invalid dtype: " <> badDesc

      notRndDt dti = throwEdh ets UsageError $ "not a numeric dtype: " <> dti

      createRandomCol :: EdhValue -> EdhValue -> STM ()
      createRandomCol !lowerValue !upperValue = do
        let createDevCol :: DeviceDataType -> STM ()
            createDevCol !dt = device'data'type'as'of'random
              dt
              (notRndDt $ device'data'type'ident dt)
              $ \(_ :: TypeRep a) -> runEdhTx ets $
                fromEdh lowerValue $ \ !lower ->
                  fromEdh upperValue $ \ !upper ->
                    if lower == upper
                      then throwEdhTx UsageError "random range is zero-width"
                      else edhContIO $ do
                        let (!lower', !upper') =
                              if lower < upper
                                then (lower, upper)
                                else (upper, lower)
                        !p <- callocArray @a size
                        !fp <- newForeignPtr finalizerFree p
                        let fillRng :: Int -> IO ()
                            fillRng !i =
                              if i >= size
                                then return ()
                                else do
                                  pokeElemOff p i =<< randomRIO (lower', upper')
                                  fillRng (i + 1)
                        fillRng 0
                        atomically $ do
                          let !cs = DeviceArray size fp
                          !csv <- newTMVar cs
                          !clv <- newTVar size
                          let !col = InMemDevCol csv clv
                          edhCreateHostObj'
                            colClass
                            (toDyn $ someColumn col)
                            [dto]
                            >>= exitEdh ets exit . EdhObject

            createDirCol :: DirectDataType -> STM ()
            createDirCol !dt = direct'data'type'as'of'random
              dt
              (notRndDt $ direct'data'type'ident dt)
              $ \(_ :: TypeRep a) -> runEdhTx ets $
                fromEdh lowerValue $ \ !lower ->
                  fromEdh upperValue $ \ !upper ->
                    if lower == upper
                      then throwEdhTx UsageError "random range is zero-width"
                      else edhContIO $ do
                        let (!lower', !upper') =
                              if lower < upper
                                then (lower, upper)
                                else (upper, lower)
                        (iov :: MV.IOVector a) <- MV.new size
                        let fillRng :: Int -> IO ()
                            fillRng !i =
                              if i >= size
                                then return ()
                                else do
                                  MV.unsafeWrite iov i
                                    =<< randomRIO (lower', upper')
                                  fillRng (i + 1)
                        fillRng 0
                        atomically $ do
                          let !cs = DirectArray iov
                          !csv <- newTMVar cs
                          !clv <- newTVar size
                          let !col = InMemDirCol csv clv
                          edhCreateHostObj'
                            colClass
                            (toDyn $ someColumn col)
                            [dto]
                            >>= exitEdh ets exit . EdhObject

        withDataType dto badDtype createDevCol createDirCol

{-

    castObjectStore dto >>= \case
      Nothing -> throwEdh ets UsageError "invalid dtype"
      Just (_, !dt) -> case edhUltimate rngSpec of
        EdhRange !lower !upper ->
          createRandomCol dt (edhBoundValue lower) (edhBoundValue upper)
        _ -> parseEdhIndex ets (edhUltimate rngSpec) $ \case
          Right (EdhIndex !stop) ->
            createRandomCol dt (EdhDecimal 0) (EdhDecimal $ fromIntegral stop)
          Right (EdhSlice !start (Just !stopN) Nothing) ->
            createRandomCol
              dt
              (EdhDecimal $ fromIntegral $ fromMaybe 0 start)
              (EdhDecimal $ fromIntegral stopN)
          Left !err -> edhValueDesc ets rngSpec $ \ !rngDesc ->
            throwEdh ets UsageError $
              "invalid random range " <> rngDesc <> " - " <> err
          _ -> edhValueDesc ets rngSpec $ \ !rngDesc ->
            throwEdh ets UsageError $
              "invalid random range " <> rngDesc
    where
      createRandomCol :: DataType -> EdhValue -> EdhValue -> STM ()
      createRandomCol !dt !lower !upper =
        resolveNumDataType ets (data'type'identifier dt) $ \ !ndt ->
          flat'new'random'array ndt ets size lower upper $ \ !cs -> do
            !csv <- newTVar cs
            !clv <- newTVar $ flatArrayCapacity cs
            let !col = Column $ InMemColumn dt csv clv
            edhCreateHostObj colClass col >>= exitEdh ets exit . EdhObject

-- TODO impl. `linspace` following:
--      https://numpy.org/doc/stable/reference/generated/numpy.linspace.html
-- Note it can be more exact by stepping with LosslessDecimal

-- | resemble https://numpy.org/doc/stable/reference/generated/numpy.where.html
whereProc :: ArgsPack -> EdhHostProc
whereProc (ArgsPack [EdhObject !colBoolIdx] !kwargs) !exit !ets
  | odNull kwargs =
    castObjectStore colBoolIdx >>= \case
      Nothing ->
        throwEdh
          ets
          UsageError
          "invalid index object, need to be a column with dtype=yesno"
      Just (_, col'@(Column !col)) ->
        let dt = data'type'of'column col
         in if data'type'identifier dt /= "yesno"
              then
                throwEdh ets UsageError $
                  "invalid dtype="
                    <> data'type'identifier dt
                    <> " for where(), need to be yesno"
              else nonzeroIdxColumn ets col' $ \ !colResult ->
                edhCreateHostObj (edh'obj'class colBoolIdx) colResult
                  >>= exitEdh ets exit
                    . EdhObject
whereProc
  (ArgsPack [EdhObject !_colBoolIdx, !_trueData, !_falseData] !kwargs)
  _exit
  !ets
    | odNull kwargs = throwEdh ets UsageError "not implemented yet."
whereProc !apk _ !ets =
  throwEdh ets UsageError $ "invalid args to where()" <> T.pack (show apk)

nonzeroIdxColumn :: EdhThreadState -> Column -> (Column -> STM ()) -> STM ()
nonzeroIdxColumn !ets (Column !colMask) !exit =
  resolveNumDataType ets (data'type'identifier dtIntp) $ \ !ndt -> do
    !mcl <- read'column'length colMask
    !mcs <- view'column'data colMask
    let !ma = unsafeSliceFlatArray mcs 0 mcl
    flat'new'nonzero'array ndt ets ma $ \(!rfa, !rlen) -> do
      !csvRtn <- newTVar rfa
      !clvRtn <- newTVar rlen
      exit $ Column $ InMemColumn dtIntp csvRtn clvRtn
  where
    dtIntp = makeDeviceDataType @Int "intp"

-}
