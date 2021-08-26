module Dim.DtArts where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Monad
import Data.Dynamic
import Data.Lossless.Decimal as D
import Data.Maybe
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
              (LitExpr $ ValueLiteral rhv)
              (LitExpr $ ValueLiteral lhv)
              exit
          else
            evalInfix
              op
              (LitExpr $ ValueLiteral lhv)
              (LitExpr $ ValueLiteral rhv)
              exit

      boxInpProc :: Bool -> AttrName -> EdhValue -> EdhHostProc
      boxInpProc !flipOperands !op !other !exit !ets = runEdhTx ets $
        withColumnSelfOf @EdhValue exit $ \_objCol !col -> do
          let vecOp =
                edhContIO $
                  view'column'data col $ \(cs, cl) -> do
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
                edhContIO $
                  view'column'data col $ \(cs, cl) ->
                    view'column'data col' $ \(cs', cl') ->
                      if cl' /= cl
                        then
                          atomically $
                            throwEdh ets UsageError $
                              "column length mistmatch: "
                                <> T.pack (show cl)
                                <> " vs "
                                <> T.pack (show cl')
                        else do
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
                edhContIO $
                  view'column'data col $ \(cs, cl) -> do
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
                edhContIO $
                  view'column'data col $ \(cs, cl) ->
                    view'column'data col' $ \(cs', cl') ->
                      if cl' /= cl
                        then
                          atomically $
                            throwEdh ets UsageError $
                              "column length mistmatch: "
                                <> T.pack (show cl)
                                <> " vs "
                                <> T.pack (show cl')
                        else do
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

mkBitsSuperDt ::
  forall a.
  (Bits a, Ord a, Storable a, EdhXchg a, Typeable a) =>
  Object ->
  DataTypeIdent ->
  Scope ->
  STM Object
mkBitsSuperDt !dtYesNo !dti !outerScope = do
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
    dt = mkBitsDataType @a dti

    dtypeAllocator :: EdhObjectAllocator
    dtypeAllocator !ctorExit _ets = ctorExit Nothing dtd

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
          edhContIO $
            view'column'data col $ \(cs, cl) -> atomically $
              runEdhTx ets $
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
          edhContIO $
            view'column'data col $ \(cs, cl) ->
              view'column'data col' $ \(cs', cl') ->
                if cl' /= cl
                  then
                    atomically $
                      throwEdh ets UsageError $
                        "column length mistmatch: "
                          <> T.pack (show cl)
                          <> " vs "
                          <> T.pack (show cl')
                  else do
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
          edhContIO $
            view'column'data col $ \(cs, cl) -> atomically $
              runEdhTx ets $
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
          edhContIO $
            view'column'data col $ \(cs, cl) ->
              view'column'data col' $ \(cs', cl') ->
                if cl' /= cl
                  then
                    atomically $
                      throwEdh ets UsageError $
                        "column length mistmatch: "
                          <> T.pack (show cl)
                          <> " vs "
                          <> T.pack (show cl')
                  else do
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
          edhContIO $
            view'column'data col $ \(cs, cl) -> atomically $
              runEdhTx ets $
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
          edhContIO $
            view'column'data col $ \(cs, cl) ->
              view'column'data col' $ \(cs', cl') ->
                if cl' /= cl
                  then
                    atomically $
                      throwEdh ets UsageError $
                        "column length mistmatch: "
                          <> T.pack (show cl)
                          <> " vs "
                          <> T.pack (show cl')
                  else do
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
          edhContIO $
            view'column'data col $ \(cs, cl) -> atomically $
              runEdhTx ets $
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
          edhContIO $
            view'column'data col $ \(cs, cl) ->
              view'column'data col' $ \(cs', cl') ->
                if cl' /= cl
                  then
                    atomically $
                      throwEdh ets UsageError $
                        "column length mistmatch: "
                          <> T.pack (show cl)
                          <> " vs "
                          <> T.pack (show cl')
                  else do
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
