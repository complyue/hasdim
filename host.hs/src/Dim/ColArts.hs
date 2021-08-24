module Dim.ColArts where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Monad
import Data.Dynamic
import Data.Lossless.Decimal as D
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
              ("(&&)", EdhMethod, wrapHostProc $ devColOpProc @YesNo (.&.)),
              ("(&&.)", EdhMethod, wrapHostProc $ devColOpProc @YesNo (.&.)),
              ("(||)", EdhMethod, wrapHostProc $ devColOpProc @YesNo (.|.)),
              ("(||.)", EdhMethod, wrapHostProc $ devColOpProc @YesNo (.|.)),
              ("(&&=)", EdhMethod, wrapHostProc $ colInpProc @YesNo (.&.)),
              ("(||=)", EdhMethod, wrapHostProc $ colInpProc @YesNo (.|.)),
              ("__eq__", EdhMethod, wrapHostProc dtypeEqProc)
            ]
      ]
  let !clsArts = clsMths ++ [(AttrByName "__repr__", EdhString dti)]
  iopdUpdate clsArts $ edh'scope'entity clsScope
  return dtYesNo
  where
    !dtd = HostStore $ toDyn dt
    dt :: DataType YesNo
    dt = mkIntDataType @YesNo dti

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
      boxInpProc !flipOperands !op !other !exit !ets = runEdhTx ets $
        withColumnSelfOf @EdhValue exit $ \_objCol !col -> do
          let vecOp =
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
                Object ->
                c' EdhValue ->
                EdhTx
              elemOp _ col' =
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
      boxApOpProc !flipOperands !op !other !exit !ets = runEdhTx ets $
        withColumnSelfOf @EdhValue exit $ \ !objCol !col -> do
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

              vecOp =
                view'column'data col $ \(cs, cl) -> edhContIO $ do
                  (iov, csResult) <- newDirectArray @EdhValue cl
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
                Object ->
                c' EdhValue ->
                EdhTx
              elemOp _ col' =
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
                        (iov, csResult) <- newDirectArray @EdhValue cl
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
    !dtd = HostStore $ toDyn dt
    dt :: DataType EdhValue
    dt = mkBoxDataType dti defv (Just EdhDecimal)

    dtypeAllocator :: EdhObjectAllocator
    dtypeAllocator !ctorExit _ets = ctorExit Nothing dtd

mkRealFracSuperDt ::
  forall a.
  (RealFrac a, Random a, Eq a, EdhXchg a, Typeable a) =>
  Object ->
  DataTypeIdent ->
  a ->
  Maybe (D.Decimal -> a) ->
  Scope ->
  STM Object
mkRealFracSuperDt !dtYesNo !dti !defv !maybeFromDec !outerScope = do
  !dtCls <- mkHostClass outerScope dti (allocEdhObj dtypeAllocator) [] $
    \ !clsScope -> do
      !clsMths <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc clsScope vc nm hp
            | (nm, vc, hp) <-
                [ ( "(==)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (==)
                  ),
                  ( "(==.)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (==)
                  ),
                  ( "(!=)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (/=)
                  ),
                  ( "(!=.)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (/=)
                  ),
                  ( "(>=)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (>=)
                  ),
                  ( "(>=.)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (<=)
                  ),
                  ( "(<=)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (<=)
                  ),
                  ( "(<=.)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (>=)
                  ),
                  ( "(>)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (>)
                  ),
                  ( "(>.)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (<)
                  ),
                  ( "(<)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (<)
                  ),
                  ( "(<.)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (>)
                  ),
                  ( "(+)",
                    EdhMethod,
                    wrapHostProc $ dirColOpProc @a (+)
                  ),
                  ( "(+.)",
                    EdhMethod,
                    wrapHostProc $ dirColOpProc @a (+)
                  ),
                  ( "(+=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc @a (+)
                  ),
                  ( "(-)",
                    EdhMethod,
                    wrapHostProc $ dirColOpProc @a (-)
                  ),
                  ( "(-.)",
                    EdhMethod,
                    wrapHostProc $ dirColOpProc @a (flip (-))
                  ),
                  ( "(-=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc @a (-)
                  ),
                  ( "(*)",
                    EdhMethod,
                    wrapHostProc $ dirColOpProc @a (*)
                  ),
                  ( "(*.)",
                    EdhMethod,
                    wrapHostProc $ dirColOpProc @a (*)
                  ),
                  ( "(*=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc @a (*)
                  ),
                  ( "(/)",
                    EdhMethod,
                    wrapHostProc $ dirColOpProc @a (/)
                  ),
                  ( "(/.)",
                    EdhMethod,
                    wrapHostProc $ dirColOpProc @a (flip (/))
                  ),
                  ( "(/=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc @a (/)
                  ),
                  ( "(//)",
                    EdhMethod,
                    wrapHostProc $
                      dirColOpProc @a (\ !x !y -> fromInteger $ floor $ x / y)
                  ),
                  ( "(//.)",
                    EdhMethod,
                    wrapHostProc $
                      dirColOpProc @a (\ !x !y -> fromInteger $ floor $ y / x)
                  ),
                  ( "(//=)",
                    EdhMethod,
                    wrapHostProc $
                      colInpProc @a (\ !x !y -> fromInteger $ floor $ x / y)
                  ),
                  ( "(**)",
                    EdhMethod,
                    wrapHostProc $ dirColOpProc @a fracPow
                  ),
                  ( "(**.)",
                    EdhMethod,
                    wrapHostProc $ dirColOpProc @a $ flip fracPow
                  ),
                  ( "(**=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc @a fracPow
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
    !dtd = HostStore $ toDyn dt
    dt :: DataType a
    dt = mkRealFracDataType @a dti defv maybeFromDec

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
                    wrapHostProc $ colCmpProc @a dtYesNo (==)
                  ),
                  ( "(==.)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (==)
                  ),
                  ( "(!=)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (/=)
                  ),
                  ( "(!=.)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (/=)
                  ),
                  ( "(>=)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (>=)
                  ),
                  ( "(>=.)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (<=)
                  ),
                  ( "(<=)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (<=)
                  ),
                  ( "(<=.)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (>=)
                  ),
                  ( "(>)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (>)
                  ),
                  ( "(>.)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (<)
                  ),
                  ( "(<)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (<)
                  ),
                  ( "(<.)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (>)
                  ),
                  ( "(+)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc @a (+)
                  ),
                  ( "(+.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc @a (+)
                  ),
                  ( "(+=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc @a (+)
                  ),
                  ( "(-)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc @a (-)
                  ),
                  ( "(-.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc @a (flip (-))
                  ),
                  ( "(-=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc @a (-)
                  ),
                  ( "(*)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc @a (*)
                  ),
                  ( "(*.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc @a (*)
                  ),
                  ( "(*=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc @a (*)
                  ),
                  ( "(/)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc @a (/)
                  ),
                  ( "(/.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc @a (flip (/))
                  ),
                  ( "(/=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc @a (/)
                  ),
                  -- TODO reason about this:
                  -- https://stackoverflow.com/questions/38588815/rounding-errors-in-python-floor-division
                  ( "(//)",
                    EdhMethod,
                    wrapHostProc $
                      dirColOpProc @a (\ !x !y -> fromInteger $ floor $ x / y)
                  ),
                  ( "(//.)",
                    EdhMethod,
                    wrapHostProc $
                      dirColOpProc @a (\ !x !y -> fromInteger $ floor $ y / x)
                  ),
                  ( "(//=)",
                    EdhMethod,
                    wrapHostProc $
                      colInpProc @a (\ !x !y -> fromInteger $ floor $ x / y)
                  ),
                  ( "(**)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc @a (**)
                  ),
                  ( "(**.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc @a (flip (**))
                  ),
                  ( "(**=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc @a (**)
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
    !dtd = HostStore $ toDyn dt
    dt :: DataType a
    dt = mkFloatDataType @a dti

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
                    wrapHostProc $ colCmpProc @a dtYesNo (==)
                  ),
                  ( "(==.)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (==)
                  ),
                  ( "(!=)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (/=)
                  ),
                  ( "(!=.)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (/=)
                  ),
                  ( "(>=)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (>=)
                  ),
                  ( "(>=.)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (<=)
                  ),
                  ( "(<=)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (<=)
                  ),
                  ( "(<=.)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (>=)
                  ),
                  ( "(>)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (>)
                  ),
                  ( "(>.)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (<)
                  ),
                  ( "(<)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (<)
                  ),
                  ( "(<.)",
                    EdhMethod,
                    wrapHostProc $ colCmpProc @a dtYesNo (>)
                  ),
                  ( "(+)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc @a (+)
                  ),
                  ( "(+.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc @a (+)
                  ),
                  ( "(+=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc @a (+)
                  ),
                  ( "(-)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc @a (-)
                  ),
                  ( "(-.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc @a (flip (-))
                  ),
                  ( "(-=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc @a (-)
                  ),
                  ( "(*)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc @a (*)
                  ),
                  ( "(*.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc @a (*)
                  ),
                  ( "(*=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc @a (*)
                  ),
                  ( "(/)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc @a div
                  ),
                  ( "(/.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc @a (flip div)
                  ),
                  ( "(/=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc @a div
                  ),
                  ( "(//)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc @a div
                  ),
                  ( "(//.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc @a (flip div)
                  ),
                  ( "(//=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc @a div
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
                    wrapHostProc $ devColOpProc @a (.&.)
                  ),
                  ( "(&&.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc @a (.&.)
                  ),
                  ( "(||)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc @a (.|.)
                  ),
                  ( "(||.)",
                    EdhMethod,
                    wrapHostProc $ devColOpProc @a (.|.)
                  ),
                  ( "(&&=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc @a (.&.)
                  ),
                  ( "(||=)",
                    EdhMethod,
                    wrapHostProc $ colInpProc @a (.|.)
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
    !dtd = HostStore $ toDyn dt
    dt :: DataType a
    dt = mkIntDataType @a dti

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
colCmpProc !dtYesNo !cmp !other !exit !ets = runEdhTx ets $
  withColumnSelfOf @a exit $ \ !objCol !col -> do
    let exitWithResult ::
          Typeable (InMemDevCol YesNo) => InMemDevCol YesNo -> STM ()
        exitWithResult !colResult =
          edhCreateHostObj'
            (edh'obj'class objCol)
            (toDyn $ someColumn colResult)
            [dtYesNo]
            >>= exitEdh ets exit . EdhObject

        vecOp =
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

        elemOp ::
          forall c' f'. ManagedColumn c' f' a => Object -> c' a -> EdhTx
        elemOp _ col' =
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
devColOpProc !op !other !exit !ets = runEdhTx ets $
  withColumnSelfOf @a exit $ \ !objCol !col -> do
    let exitWithNewClone ::
          forall c' f'.
          (ManagedColumn c' f' a, Typeable (c' a)) =>
          c' a ->
          STM ()
        exitWithNewClone !colResult =
          edhCloneHostObj ets objCol objCol (someColumn colResult) $
            \ !newObj -> exitEdh ets exit $ EdhObject newObj

        vecOp =
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

        elemOp ::
          forall c' f'. ManagedColumn c' f' a => Object -> c' a -> EdhTx
        elemOp _ col' =
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
dirColOpProc !op !other !exit !ets = runEdhTx ets $
  withColumnSelfOf @a exit $ \ !objCol !col -> do
    let exitWithNewClone ::
          forall c' f'.
          (ManagedColumn c' f' a, Typeable (c' a)) =>
          c' a ->
          STM ()
        exitWithNewClone !colResult =
          edhCloneHostObj ets objCol objCol (someColumn colResult) $
            \ !newObj -> exitEdh ets exit $ EdhObject newObj

        vecOp =
          view'column'data col $ \(cs, cl) ->
            fromEdh' @a other naExit $ \rhv -> edhContIO $ do
              (iov, csResult) <- newDirectArray @a cl
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

        elemOp ::
          forall c' f'. ManagedColumn c' f' a => Object -> c' a -> EdhTx
        elemOp _ col' =
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
                  (iov, csResult) <- newDirectArray @a cl
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
colInpProc !op !other !exit !ets = runEdhTx ets $
  withColumnSelfOf @a exit $ \_objCol !col -> do
    let vecOp =
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

        elemOp ::
          forall c' f'. ManagedColumn c' f' a => Object -> c' a -> EdhTx
        elemOp _ col' =
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
            "Column capacity can not be negative: " <> T.pack (show ctorCap)
        | ctorLen < 0 =
          throwEdh etsCtor UsageError $
            "Column length can not be negative: " <> T.pack (show ctorLen)
        | ctorLen > ctorCap =
          throwEdh etsCtor UsageError $
            "Column length can not be larger than capacity: "
              <> T.pack (show ctorLen)
              <> " vs "
              <> T.pack (show ctorCap)
        | otherwise = withDataType dto badDtype $ \case
          DeviceDt dt ->
            device'data'type'holder dt $ \(_ :: TypeRep a) ->
              runEdhTx etsCtor $
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
          DirectDt dt ->
            direct'data'defv'holder dt $ \(fill'val :: a) ->
              runEdhTx etsCtor $
                edhContIO $ do
                  (_iov, !cs) <- newDirectArray' @a fill'val ctorCap
                  atomically $ do
                    !csv <- newTMVar cs
                    !clv <- newTVar ctorLen
                    ctorExit Nothing $
                      HostStore $
                        toDyn $
                          SomeColumn (typeRep @DirectArray) $
                            InMemDirCol @a csv clv
        where
          badDtype = edhSimpleDesc etsCtor (EdhObject dto) $ \ !badDesc ->
            throwEdh etsCtor UsageError $ "invalid dtype: " <> badDesc

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

    withThisColumn :: (Object -> SomeColumn -> EdhTx) -> EdhTx
    withThisColumn !exit !ets = case fromDynamic =<< dynamicHostData this of
      Nothing -> throwEdh ets EvalError "bug: this is not a Column"
      Just !col -> exitEdh ets (exit this) col
      where
        this = edh'scope'this $ contextScope $ edh'context ets

    colCapProc :: EdhHostProc
    colCapProc !exit = withThisColumn $ \_this (SomeColumn _ !col) ->
      view'column'data col $ \(cs, _cl) ->
        exitEdhTx exit $ EdhDecimal $ fromIntegral $ array'capacity cs

    colLenProc :: EdhHostProc
    colLenProc !exit = withThisColumn $ \_this (SomeColumn _ !col) ->
      read'column'length col $ \ !len ->
        exitEdhTx exit $ EdhDecimal $ fromIntegral len

    colGrowProc :: "newCap" !: Int -> EdhHostProc
    colGrowProc (mandatoryArg -> !newCap) !exit !ets =
      runEdhTx ets $
        if newCap < 0
          then
            throwEdhTx UsageError $
              "invalid newCap: " <> T.pack (show newCap)
          else withThisColumn $ \_this (SomeColumn _ !col) ->
            grow'column'capacity col newCap $
              const $
                exitEdhTx exit $
                  EdhObject $ edh'scope'that $ contextScope $ edh'context ets

    colMarkLenProc :: "newLen" !: Int -> EdhHostProc
    colMarkLenProc (mandatoryArg -> !newLen) !exit !ets = runEdhTx ets $
      withThisColumn $ \_this (SomeColumn _ !col) ->
        mark'column'length col newLen $
          const $
            exitEdhTx exit $
              EdhObject $ edh'scope'that $ contextScope $ edh'context ets

    colBlobProc :: EdhHostProc
    colBlobProc !exit = withThisColumn $ \_this (SomeColumn _ !col) ->
      view'column'data col $
        \(cs, cl) -> array'as'blob cs cl (exitEdhTx exit edhNA) $ \ !bytes ->
          exitEdhTx exit $ EdhBlob bytes

    colJsonProc :: EdhHostProc
    colJsonProc !exit !ets = runEdhTx ets $
      withThisColumn $ \_this (SomeColumn _ !col) ->
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
    colReprProc !exit = withThisColumn $ \ !this (SomeColumn _ !col) !ets ->
      getColumnDtype ets this $ \ !dto -> runEdhTx ets $
        edhValueReprTx (EdhObject dto) $
          \ !dtRepr -> view'column'data col $ \(!cs, !cl) -> do
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
    colShowProc !exit =
      withThisColumn $ \ !this (SomeColumn _ !col) !ets ->
        getColumnDtype ets this $ \ !dto -> runEdhTx ets $
          edhValueReprTx (EdhObject dto) $
            \ !dtRepr -> view'column'data col $ \(!cs, !cl) -> do
              let !colRepr =
                    "Column( capacity= "
                      <> T.pack (show $ array'capacity cs)
                      <> ", length= "
                      <> T.pack (show cl)
                      <> ", dtype= "
                      <> dtRepr
                      <> " )"
                  readElem i !elemExit = do
                    !hv <- array'reader cs i
                    atomically $
                      runEdhTx ets $
                        toEdh hv $
                          \ !v -> edhValueStrTx v $ edhContIO . elemExit
              edhContIO $
                showColContent cl readElem $ \ !contentLines ->
                  atomically $
                    exitEdh ets exit $
                      EdhString $ colRepr <> "\n" <> contentLines

    -- TODO impl. this following:
    --      https://pandas.pydata.org/pandas-docs/stable/reference/api/pandas.Series.describe.html
    colDescProc :: EdhHostProc
    colDescProc !exit = withThisColumn $ \ !this (SomeColumn _ !col) !ets ->
      getColumnDtype ets this $ \ !dto -> runEdhTx ets $
        edhValueReprTx (EdhObject dto) $
          \ !dtRepr -> view'column'data col $ \(!cs, !cl) -> do
            let colRepr =
                  "Column( capacity= "
                    <> T.pack (show $ array'capacity cs)
                    <> ", length= "
                    <> T.pack (show cl)
                    <> ", dtype= "
                    <> dtRepr
                    <> " )"
            exitEdhTx exit $
              EdhString $
                " 🚧 Statistical Description of Column data,\n"
                  <> " 🏗  like Pandas' describe(), is yet to be implemented.\n"
                  <> colRepr

    colIdxReadProc :: EdhValue -> EdhHostProc
    colIdxReadProc !idxVal !exit = withThisColumn $ \ !this !col -> do
      let withBoolIdx ::
            forall c f.
            ManagedColumn c f YesNo =>
            Object ->
            c YesNo ->
            EdhTx
          withBoolIdx _ !idxCol =
            extractColumnBool this col idxCol $ \(!newColObj, _newCol) ->
              exitEdhTx exit $ EdhObject newColObj

          withIntpIdx ::
            forall c f.
            ManagedColumn c f Int =>
            Object ->
            c Int ->
            EdhTx
          withIntpIdx _ !idxCol =
            extractColumnFancy this col idxCol $ \(!newColObj, _newCol) ->
              exitEdhTx exit $ EdhObject newColObj

          withEdhIdx :: EdhTx
          withEdhIdx !ets = parseEdhIndex ets idxVal $ \case
            Left !err -> throwEdh ets UsageError err
            Right !idx -> case idx of
              EdhIndex !i -> runEdhTx ets $ case col of
                SomeColumn _ col' -> view'column'data col' $
                  \(!cs, _cl) ->
                    edhContIO $
                      array'reader cs i >>= \ !ev ->
                        atomically $
                          runEdhTx ets $
                            toEdh ev $ \ !elemVal ->
                              exitEdhTx exit elemVal
              EdhAny -> exitEdh ets exit $ EdhObject that
              EdhAll -> exitEdh ets exit $ EdhObject that
              EdhSlice !start !stop !step -> runEdhTx ets $ case col of
                SomeColumn _ col' -> view'column'data col' $
                  \(_cs, !cl) _ets ->
                    edhRegulateSlice ets cl (start, stop, step) $
                      \(!iStart, !iStop, !iStep) ->
                        runEdhTx ets $
                          sliceColumn this col iStart iStop iStep $
                            \(!newColObj, _newCol) ->
                              exitEdhTx exit $ EdhObject newColObj
            where
              that = edh'scope'that $ contextScope $ edh'context ets

      withColumnOf' @YesNo
        idxVal
        (withColumnOf' @Int idxVal withEdhIdx withIntpIdx)
        withBoolIdx

    colIdxWriteProc :: EdhValue -> EdhValue -> EdhHostProc
    colIdxWriteProc !idxVal !other !exit = withThisColumn $ \_this !col ->
      idxAssignColumn col idxVal other $ exitEdhTx exit other

    colCopyProc :: "capacity" ?: Int -> EdhHostProc
    colCopyProc (optionalArg -> !maybeCap) !exit !ets = runEdhTx ets $
      withThisColumn $ \ !this (SomeColumn _ !col) ->
        read'column'length col $ \ !cl ->
          copy'column'slice
            col
            (fromMaybe cl maybeCap)
            0
            cl
            1
            $ \(disp, col') _ets -> case disp of
              StayComposed ->
                edhCloneHostObj ets this this col' $
                  \ !newColObj -> exitEdh ets exit $ EdhObject newColObj
              ExtractAlone -> getColumnDtype ets this $ \ !dto ->
                edhCreateHostObj'
                  (edh'obj'class this)
                  (toDyn col')
                  [dto]
                  >>= \ !newColObj -> exitEdh ets exit $ EdhObject newColObj

    colDtypeProc :: EdhHostProc
    colDtypeProc !exit !ets =
      getColumnDtype ets this $ exitEdh ets exit . EdhObject
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
            withDataType dto badDtype $ \case
              DeviceDt dt -> device'data'type'as'of'num
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
              DirectDt dt -> do
                let tryFromDec :: STM ()
                    tryFromDec = direct'data'type'from'num
                      dt
                      (notNumDt $ direct'data'type'ident dt)
                      $ \ !fromDec -> runEdhTx ets $
                        edhContIO $ do
                          (iov :: MV.IOVector a) <- MV.new len
                          let fillRng :: Int -> Int -> IO ()
                              fillRng !n !i =
                                if i >= len
                                  then return ()
                                  else do
                                    MV.unsafeWrite iov i $
                                      fromDec $ fromIntegral n
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

                direct'data'type'as'of'num dt tryFromDec $
                  \(_ :: TypeRep a) -> runEdhTx ets $
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
        withDataType dto badDtype $ \case
          DeviceDt dt -> device'data'type'as'of'random
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
          DirectDt dt -> direct'data'type'as'of'random
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

-- TODO impl. `linspace` following:
--      https://numpy.org/doc/stable/reference/generated/numpy.linspace.html
-- Note it can be more exact by stepping with LosslessDecimal

-- | resemble https://numpy.org/doc/stable/reference/generated/numpy.where.html
whereProc :: Object -> Object -> ArgsPack -> EdhHostProc
whereProc !colClass !dtIntp (ArgsPack [EdhObject !colYesNo] !kwargs) !exit !ets
  | odNull kwargs = runEdhTx ets $
    withColumnOf @YesNo colYesNo naExit $ \_ !col ->
      view'column'data col $ \(cs, cl) -> edhContIO $ do
        !p <- callocArray @Int cl
        !fp <- newForeignPtr finalizerFree p
        let fillIdxs :: Int -> Int -> IO Int
            fillIdxs !n !i =
              if i >= cl
                then return n
                else
                  array'reader cs i >>= \case
                    YesNo 0 -> fillIdxs n (i + 1)
                    _ -> do
                      pokeElemOff p n i
                      fillIdxs (n + 1) (i + 1)
        !len <- fillIdxs 0 0
        atomically $ do
          let !cs' = DeviceArray cl fp
          !csv <- newTMVar cs'
          !clv <- newTVar len
          let !col' = InMemDevCol csv clv
          edhCreateHostObj'
            colClass
            (toDyn $ someColumn col')
            [dtIntp]
            >>= exitEdh ets exit . EdhObject
  where
    naExit = throwEdhTx UsageError "not a `yesno` column"
whereProc
  _colClass
  _dtIntp
  (ArgsPack [EdhObject !_colBoolIdx, !_trueData, !_falseData] !kwargs)
  _exit
  !ets
    | odNull kwargs = throwEdh ets UsageError "not implemented yet."
whereProc _colClass _dtIntp !apk _ !ets =
  throwEdh ets UsageError $ "invalid args to where()" <> T.pack (show apk)
