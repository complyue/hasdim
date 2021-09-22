module Dim.ColDtArts where

-- import           Debug.Trace

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Data.Dynamic
import Data.Lossless.Decimal as D
import Data.Maybe
import qualified Data.Text as T
import Data.Unique
import qualified Data.Vector.Mutable as MV
import Dim.Column
import Dim.DataType
import Dim.FlatArray
import Dim.InMem
import Dim.XCHG
import Foreign hiding (void)
import Foreign.ForeignPtr.Unsafe
import GHC.Float
import Language.Edh.MHI
import System.Random
import Prelude

mkYesNoColDt :: DataTypeIdent -> Edh Object
mkYesNoColDt !dti = do
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
                  colCmpProc dtYesNo ((==) :: YesNo -> YesNo -> Bool)
              ),
              ( "(==.)",
                EdhMethod,
                wrapEdhProc $
                  colCmpProc dtYesNo ((==) :: YesNo -> YesNo -> Bool)
              ),
              ( "(!=)",
                EdhMethod,
                wrapEdhProc $
                  colCmpProc dtYesNo ((/=) :: YesNo -> YesNo -> Bool)
              ),
              ( "(!=.)",
                EdhMethod,
                wrapEdhProc $
                  colCmpProc dtYesNo ((/=) :: YesNo -> YesNo -> Bool)
              ),
              ("(&&)", EdhMethod, wrapEdhProc $ devColOpProc @YesNo (.&.)),
              ("(&&.)", EdhMethod, wrapEdhProc $ devColOpProc @YesNo (.&.)),
              ("(||)", EdhMethod, wrapEdhProc $ devColOpProc @YesNo (.|.)),
              ("(||.)", EdhMethod, wrapEdhProc $ devColOpProc @YesNo (.|.)),
              ("(&&=)", EdhMethod, wrapEdhProc $ colInpProc @YesNo (.&.)),
              ("(||=)", EdhMethod, wrapEdhProc $ colInpProc @YesNo (.|.)),
              ("__eq__", EdhMethod, wrapEdhProc dtypeEqProc)
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

mkBoxColDt :: DataTypeIdent -> EdhValue -> Edh Object
mkBoxColDt !dti !defv = do
  !dtCls <- mkEdhClass dti (allocObjM dtypeAllocator) [] $ pure ()
  !idObj <- newUniqueEdh
  !supersVar <- newTVarEdh []
  let !dtBox =
        Object
          { edh'obj'ident = idObj,
            edh'obj'store = dtd,
            edh'obj'class = dtCls,
            edh'obj'supers = supersVar
          }

      evalOp ::
        Bool -> AttrName -> EdhValue -> EdhValue -> Edh EdhValue
      evalOp !flipOperands !op lhv rhv =
        if flipOperands
          then
            evalInfixM
              op
              (LitExpr $ ValueLiteral rhv)
              (LitExpr $ ValueLiteral lhv)
          else
            evalInfixM
              op
              (LitExpr $ ValueLiteral lhv)
              (LitExpr $ ValueLiteral rhv)

      boxInpProc :: Bool -> AttrName -> EdhValue -> Edh EdhValue
      boxInpProc !flipOperands !op !other =
        withColumnSelfOf @EdhValue $ \_objCol !col -> do
          let vecOp :: Edh ()
              vecOp =
                liftEIO $
                  view'column'data col >>= \(cs, cl) -> do
                    let go i
                          | i < 0 = return ()
                          | otherwise = do
                            lhev <- liftIO $ array'reader cs i
                            !result <-
                              liftEdh $ evalOp flipOperands op lhev other
                            liftIO $ array'writer cs i result
                            go $ i - 1
                    go $ cl - 1

              elemOp ::
                forall c' f'.
                ManagedColumn c' f' EdhValue =>
                Object ->
                c' EdhValue ->
                Edh ()
              elemOp _ col' = liftEIO $ do
                (cs, cl) <- view'column'data col
                (cs', cl') <- view'column'data col'
                if cl' /= cl
                  then
                    throwEIO UsageError $
                      "column length mistmatch: "
                        <> T.pack (show cl)
                        <> " vs "
                        <> T.pack (show cl')
                  else do
                    let go i
                          | i < 0 = return ()
                          | otherwise = do
                            (lhev, rhev) <- liftIO $ do
                              lhev <- array'reader cs i
                              rhev <- array'reader cs' i
                              return (lhev, rhev)
                            !result <-
                              liftEdh $ evalOp flipOperands op lhev rhev
                            liftIO $ array'writer cs i result
                            go $ i - 1
                    go $ cl - 1

          withColumnOf' @EdhValue other elemOp <|> vecOp
          EdhObject . edh'scope'that . contextScope . edh'context
            <$> edhThreadState

      boxApOpProc :: Bool -> AttrName -> EdhValue -> Edh EdhValue
      boxApOpProc !flipOperands !op !other =
        withColumnSelfOf @EdhValue $ \ !objCol !col -> do
          let exitWithResult ::
                Typeable (InMemDirCol EdhValue) =>
                InMemDirCol EdhValue ->
                EIO EdhValue
              exitWithResult !colResult =
                liftEdh $
                  EdhObject
                    <$> createHostObjectM'
                      (edh'obj'class objCol)
                      (toDyn $ someColumn colResult)
                      [dtBox]

              vecOp = liftEIO $ do
                (cs, cl) <- view'column'data col
                (iov, csResult) <- liftIO $ newDirectArray @EdhValue cl
                let go i
                      | i < 0 = do
                        csvResult <- newTMVarEIO csResult
                        clvResult <- newTVarEIO cl
                        exitWithResult $ InMemDirCol csvResult clvResult
                      | otherwise = do
                        lhev <- liftIO $ array'reader cs i
                        !result <-
                          liftEdh $ evalOp flipOperands op lhev other
                        liftIO $ MV.unsafeWrite iov i result
                        go $ i - 1
                go $ cl - 1

              elemOp ::
                forall c' f'.
                ManagedColumn c' f' EdhValue =>
                Object ->
                c' EdhValue ->
                Edh EdhValue
              elemOp _ col' = liftEIO $ do
                (cs, cl) <- view'column'data col
                (cs', cl') <- view'column'data col'
                if cl' /= cl
                  then
                    throwEIO UsageError $
                      "column length mistmatch: "
                        <> T.pack (show cl)
                        <> " vs "
                        <> T.pack (show cl')
                  else do
                    (iov, csResult) <- liftIO $ newDirectArray @EdhValue cl
                    let go i
                          | i < 0 = do
                            csvResult <- newTMVarEIO csResult
                            clvResult <- newTVarEIO cl
                            exitWithResult $ InMemDirCol csvResult clvResult
                          | otherwise = do
                            (lhev, rhev) <- liftIO $ do
                              lhev <- array'reader cs i
                              rhev <- array'reader cs' i
                              return (lhev, rhev)
                            !result <-
                              liftEdh $ evalOp flipOperands op lhev rhev
                            liftIO $ MV.unsafeWrite iov i result
                            go $ i - 1
                    go $ cl - 1

          withColumnOf' @EdhValue other elemOp <|> vecOp

  !clsMths <-
    sequence $
      [ (AttrByName nm,) <$> mkEdhProc vc nm hp
        | (nm, vc, hp) <-
            [ ("(==)", EdhMethod, wrapEdhProc $ boxApOpProc False "=="),
              ("(==.)", EdhMethod, wrapEdhProc $ boxApOpProc True "=="),
              ("(!=)", EdhMethod, wrapEdhProc $ boxApOpProc False "!="),
              ("(!=.)", EdhMethod, wrapEdhProc $ boxApOpProc True "!="),
              ("(>=)", EdhMethod, wrapEdhProc $ boxApOpProc False ">="),
              ("(>=.)", EdhMethod, wrapEdhProc $ boxApOpProc True ">="),
              ("(<=)", EdhMethod, wrapEdhProc $ boxApOpProc False "<="),
              ("(<=.)", EdhMethod, wrapEdhProc $ boxApOpProc True "<="),
              ("(>)", EdhMethod, wrapEdhProc $ boxApOpProc False ">"),
              ("(>.)", EdhMethod, wrapEdhProc $ boxApOpProc True ">"),
              ("(<)", EdhMethod, wrapEdhProc $ boxApOpProc False "<"),
              ("(<.)", EdhMethod, wrapEdhProc $ boxApOpProc True "<"),
              ("(+)", EdhMethod, wrapEdhProc $ boxApOpProc False "+"),
              ("(+.)", EdhMethod, wrapEdhProc $ boxApOpProc True "+"),
              ("(-)", EdhMethod, wrapEdhProc $ boxApOpProc False "-"),
              ("(-.)", EdhMethod, wrapEdhProc $ boxApOpProc True "-"),
              ("(*)", EdhMethod, wrapEdhProc $ boxApOpProc False "*"),
              ("(*.)", EdhMethod, wrapEdhProc $ boxApOpProc True "*"),
              ("(/)", EdhMethod, wrapEdhProc $ boxApOpProc False "/"),
              ("(/.)", EdhMethod, wrapEdhProc $ boxApOpProc True "/"),
              ("(//)", EdhMethod, wrapEdhProc $ boxApOpProc False "//"),
              ("(//.)", EdhMethod, wrapEdhProc $ boxApOpProc True "//"),
              ("(**)", EdhMethod, wrapEdhProc $ boxApOpProc False "**"),
              ("(**.)", EdhMethod, wrapEdhProc $ boxApOpProc True "**"),
              ("(>=)", EdhMethod, wrapEdhProc $ boxApOpProc False ">="),
              ("(>=.)", EdhMethod, wrapEdhProc $ boxApOpProc True ">="),
              ("(+=)", EdhMethod, wrapEdhProc $ boxInpProc False "+"),
              ("(-=)", EdhMethod, wrapEdhProc $ boxInpProc False "-"),
              ("(*=)", EdhMethod, wrapEdhProc $ boxInpProc False "*"),
              ("(/=)", EdhMethod, wrapEdhProc $ boxInpProc False "/"),
              ("(//=)", EdhMethod, wrapEdhProc $ boxInpProc False "//"),
              ("(**=)", EdhMethod, wrapEdhProc $ boxInpProc False "**"),
              ("__eq__", EdhMethod, wrapEdhProc dtypeEqProc)
            ]
      ]

  let !clsArts = clsMths ++ [(AttrByName "__repr__", EdhString dti)]
  !clsScope <- inlineSTM $ objectScope dtCls
  iopdUpdateEdh clsArts $ edh'scope'entity clsScope
  return dtBox
  where
    !dtd = HostStore $ toDyn dt
    dt :: DataType EdhValue
    dt = mkBoxDataType dti defv (Just EdhDecimal)

    dtypeAllocator :: Edh (Maybe Unique, ObjectStore)
    dtypeAllocator = return (Nothing, dtd)

mkRealFracColDt ::
  forall a.
  (RealFrac a, Random a, Eq a, EdhXchg a, Typeable a) =>
  Object ->
  DataTypeIdent ->
  a ->
  Maybe (D.Decimal -> a) ->
  Edh Object
mkRealFracColDt !dtYesNo !dti !defv !maybeFromDec = do
  !dtCls <- mkEdhClass dti (allocObjM dtypeAllocator) [] $ do
    !clsMths <-
      sequence $
        [ (AttrByName nm,) <$> mkEdhProc vc nm hp
          | (nm, vc, hp) <-
              [ ( "(==)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (==)
                ),
                ( "(==.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (==)
                ),
                ( "(!=)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (/=)
                ),
                ( "(!=.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (/=)
                ),
                ( "(>=)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (>=)
                ),
                ( "(>=.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (<=)
                ),
                ( "(<=)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (<=)
                ),
                ( "(<=.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (>=)
                ),
                ( "(>)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (>)
                ),
                ( "(>.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (<)
                ),
                ( "(<)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (<)
                ),
                ( "(<.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (>)
                ),
                ( "(+)",
                  EdhMethod,
                  wrapEdhProc $ dirColOpProc @a (+)
                ),
                ( "(+.)",
                  EdhMethod,
                  wrapEdhProc $ dirColOpProc @a (+)
                ),
                ( "(+=)",
                  EdhMethod,
                  wrapEdhProc $ colInpProc @a (+)
                ),
                ( "(-)",
                  EdhMethod,
                  wrapEdhProc $ dirColOpProc @a (-)
                ),
                ( "(-.)",
                  EdhMethod,
                  wrapEdhProc $ dirColOpProc @a (flip (-))
                ),
                ( "(-=)",
                  EdhMethod,
                  wrapEdhProc $ colInpProc @a (-)
                ),
                ( "(*)",
                  EdhMethod,
                  wrapEdhProc $ dirColOpProc @a (*)
                ),
                ( "(*.)",
                  EdhMethod,
                  wrapEdhProc $ dirColOpProc @a (*)
                ),
                ( "(*=)",
                  EdhMethod,
                  wrapEdhProc $ colInpProc @a (*)
                ),
                ( "(/)",
                  EdhMethod,
                  wrapEdhProc $ dirColOpProc @a (/)
                ),
                ( "(/.)",
                  EdhMethod,
                  wrapEdhProc $ dirColOpProc @a (flip (/))
                ),
                ( "(/=)",
                  EdhMethod,
                  wrapEdhProc $ colInpProc @a (/)
                ),
                ( "(//)",
                  EdhMethod,
                  wrapEdhProc $
                    dirColOpProc @a (\ !x !y -> fromInteger $ floor $ x / y)
                ),
                ( "(//.)",
                  EdhMethod,
                  wrapEdhProc $
                    dirColOpProc @a (\ !x !y -> fromInteger $ floor $ y / x)
                ),
                ( "(//=)",
                  EdhMethod,
                  wrapEdhProc $
                    colInpProc @a (\ !x !y -> fromInteger $ floor $ x / y)
                ),
                ( "(**)",
                  EdhMethod,
                  wrapEdhProc $ dirColOpProc @a fracPow
                ),
                ( "(**.)",
                  EdhMethod,
                  wrapEdhProc $ dirColOpProc @a $ flip fracPow
                ),
                ( "(**=)",
                  EdhMethod,
                  wrapEdhProc $ colInpProc @a fracPow
                ),
                ("__eq__", EdhMethod, wrapEdhProc dtypeEqProc)
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
    dt = mkRealFracDataType @a dti defv maybeFromDec

    dtypeAllocator :: Edh (Maybe Unique, ObjectStore)
    dtypeAllocator = return (Nothing, dtd)

    fracPow :: a -> a -> a
    fracPow _ 0 = 1
    fracPow x y
      -- TODO this justifies?
      | y < 0 = 0 -- to survive `Exception: Negative exponent`
      | otherwise = x ^ (floor y :: Integer)

mkFloatColDt ::
  forall a.
  (RealFloat a, Random a, Num a, Storable a, EdhXchg a, Typeable a) =>
  Object ->
  DataTypeIdent ->
  Edh Object
mkFloatColDt !dtYesNo !dti = do
  !dtCls <- mkEdhClass dti (allocObjM dtypeAllocator) [] $ do
    !clsMths <-
      sequence $
        [ (AttrByName nm,) <$> mkEdhProc vc nm hp
          | (nm, vc, hp) <-
              [ ( "(==)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (==)
                ),
                ( "(==.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (==)
                ),
                ( "(!=)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (/=)
                ),
                ( "(!=.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (/=)
                ),
                ( "(>=)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (>=)
                ),
                ( "(>=.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (<=)
                ),
                ( "(<=)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (<=)
                ),
                ( "(<=.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (>=)
                ),
                ( "(>)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (>)
                ),
                ( "(>.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (<)
                ),
                ( "(<)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (<)
                ),
                ( "(<.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (>)
                ),
                ( "(+)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (+)
                ),
                ( "(+.)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (+)
                ),
                ( "(+=)",
                  EdhMethod,
                  wrapEdhProc $ colInpProc @a (+)
                ),
                ( "(-)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (-)
                ),
                ( "(-.)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (flip (-))
                ),
                ( "(-=)",
                  EdhMethod,
                  wrapEdhProc $ colInpProc @a (-)
                ),
                ( "(*)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (*)
                ),
                ( "(*.)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (*)
                ),
                ( "(*=)",
                  EdhMethod,
                  wrapEdhProc $ colInpProc @a (*)
                ),
                ( "(/)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (/)
                ),
                ( "(/.)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (flip (/))
                ),
                ( "(/=)",
                  EdhMethod,
                  wrapEdhProc $ colInpProc @a (/)
                ),
                -- TODO reason about this:
                -- https://stackoverflow.com/questions/38588815/rounding-errors-in-python-floor-division
                ( "(//)",
                  EdhMethod,
                  wrapEdhProc $
                    dirColOpProc @a (\ !x !y -> fromInteger $ floor $ x / y)
                ),
                ( "(//.)",
                  EdhMethod,
                  wrapEdhProc $
                    dirColOpProc @a (\ !x !y -> fromInteger $ floor $ y / x)
                ),
                ( "(//=)",
                  EdhMethod,
                  wrapEdhProc $
                    colInpProc @a (\ !x !y -> fromInteger $ floor $ x / y)
                ),
                ( "(**)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (**)
                ),
                ( "(**.)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (flip (**))
                ),
                ( "(**=)",
                  EdhMethod,
                  wrapEdhProc $ colInpProc @a (**)
                ),
                ("__eq__", EdhMethod, wrapEdhProc dtypeEqProc)
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

mkIntColDt ::
  forall a.
  (Bits a, Integral a, Random a, Num a, Storable a, EdhXchg a, Typeable a) =>
  Object ->
  DataTypeIdent ->
  Edh Object
mkIntColDt !dtYesNo !dti = do
  !dtCls <- mkEdhClass dti (allocObjM dtypeAllocator) [] $ do
    !clsMths <-
      sequence $
        [ (AttrByName nm,) <$> mkEdhProc vc nm hp
          | (nm, vc, hp) <-
              [ ( "(==)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (==)
                ),
                ( "(==.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (==)
                ),
                ( "(!=)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (/=)
                ),
                ( "(!=.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (/=)
                ),
                ( "(>=)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (>=)
                ),
                ( "(>=.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (<=)
                ),
                ( "(<=)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (<=)
                ),
                ( "(<=.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (>=)
                ),
                ( "(>)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (>)
                ),
                ( "(>.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (<)
                ),
                ( "(<)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (<)
                ),
                ( "(<.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (>)
                ),
                ( "(+)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (+)
                ),
                ( "(+.)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (+)
                ),
                ( "(+=)",
                  EdhMethod,
                  wrapEdhProc $ colInpProc @a (+)
                ),
                ( "(-)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (-)
                ),
                ( "(-.)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (flip (-))
                ),
                ( "(-=)",
                  EdhMethod,
                  wrapEdhProc $ colInpProc @a (-)
                ),
                ( "(*)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (*)
                ),
                ( "(*.)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (*)
                ),
                ( "(*=)",
                  EdhMethod,
                  wrapEdhProc $ colInpProc @a (*)
                ),
                ( "(/)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a div
                ),
                ( "(/.)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (flip div)
                ),
                ( "(/=)",
                  EdhMethod,
                  wrapEdhProc $ colInpProc @a div
                ),
                ( "(//)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a div
                ),
                ( "(//.)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (flip div)
                ),
                ( "(//=)",
                  EdhMethod,
                  wrapEdhProc $ colInpProc @a div
                ),
                ( "(**)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc intPow
                ),
                ( "(**.)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc $ flip intPow
                ),
                ( "(**=)",
                  EdhMethod,
                  wrapEdhProc $ colInpProc intPow
                ),
                ( "(&&)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (.&.)
                ),
                ( "(&&.)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (.&.)
                ),
                ( "(||)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (.|.)
                ),
                ( "(||.)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (.|.)
                ),
                ( "(&&=)",
                  EdhMethod,
                  wrapEdhProc $ colInpProc @a (.&.)
                ),
                ( "(||=)",
                  EdhMethod,
                  wrapEdhProc $ colInpProc @a (.|.)
                ),
                ("__eq__", EdhMethod, wrapEdhProc dtypeEqProc)
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

mkBitsColDt ::
  forall a.
  (Bits a, Ord a, Storable a, EdhXchg a, Typeable a) =>
  Object ->
  DataTypeIdent ->
  Edh Object
mkBitsColDt !dtYesNo !dti = do
  !dtCls <- mkEdhClass dti (allocObjM dtypeAllocator) [] $ do
    !clsMths <-
      sequence $
        [ (AttrByName nm,) <$> mkEdhProc vc nm hp
          | (nm, vc, hp) <-
              [ ( "(==)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (==)
                ),
                ( "(==.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (==)
                ),
                ( "(!=)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (/=)
                ),
                ( "(!=.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (/=)
                ),
                ( "(>=)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (>=)
                ),
                ( "(>=.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (<=)
                ),
                ( "(<=)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (<=)
                ),
                ( "(<=.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (>=)
                ),
                ( "(>)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (>)
                ),
                ( "(>.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (<)
                ),
                ( "(<)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (<)
                ),
                ( "(<.)",
                  EdhMethod,
                  wrapEdhProc $ colCmpProc @a dtYesNo (>)
                ),
                ( "(&&)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (.&.)
                ),
                ( "(&&.)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (.&.)
                ),
                ( "(||)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (.|.)
                ),
                ( "(||.)",
                  EdhMethod,
                  wrapEdhProc $ devColOpProc @a (.|.)
                ),
                ( "(&&=)",
                  EdhMethod,
                  wrapEdhProc $ colInpProc @a (.&.)
                ),
                ( "(||=)",
                  EdhMethod,
                  wrapEdhProc $ colInpProc @a (.|.)
                ),
                ("__eq__", EdhMethod, wrapEdhProc dtypeEqProc)
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

colCmpProc ::
  forall a.
  (Eq a, EdhXchg a, Typeable a) =>
  Object ->
  (a -> a -> Bool) ->
  EdhValue ->
  Edh EdhValue
colCmpProc !dtYesNo !cmp !other =
  withColumnSelfOf @a $ \ !objCol !col -> do
    let exitWithResult ::
          Typeable (InMemDevCol YesNo) => InMemDevCol YesNo -> EIO EdhValue
        exitWithResult !colResult =
          liftEdh $
            EdhObject
              <$> createHostObjectM'
                (edh'obj'class objCol)
                (toDyn $ someColumn colResult)
                [dtYesNo]

        vecOp = liftEIO $ do
          (cs, cl) <- view'column'data col
          liftEdh (fromEdh' @a other) >>= \case
            Nothing -> return edhNA
            Just !rhv -> do
              csResult <- do
                (fp, csResult) <- liftIO $ newDeviceArray @YesNo cl
                let p = unsafeForeignPtrToPtr fp
                    go i
                      | i < 0 = return ()
                      | otherwise = do
                        lhev <- array'reader cs i
                        pokeElemOff p i $ yesOrNo $ cmp lhev rhv
                        go $ i - 1
                liftIO $ go $ cl - 1
                return csResult
              csvResult <- newTMVarEIO csResult
              clvResult <- newTVarEIO cl
              exitWithResult $ InMemDevCol csvResult clvResult

        elemOp ::
          forall c' f'. ManagedColumn c' f' a => Object -> c' a -> Edh EdhValue
        elemOp _ col' = liftEIO $ do
          (cs, cl) <- view'column'data col
          (cs', cl') <- view'column'data col'
          if cl' /= cl
            then
              throwEIO UsageError $
                "column length mistmatch: "
                  <> T.pack (show cl)
                  <> " vs "
                  <> T.pack (show cl')
            else do
              csResult <- do
                (fp, csResult) <- liftIO $ newDeviceArray @YesNo cl
                let p = unsafeForeignPtrToPtr fp
                    go i
                      | i < 0 = return ()
                      | otherwise = do
                        lhev <- array'reader cs i
                        rhev <- array'reader cs' i
                        pokeElemOff p i $ yesOrNo $ cmp lhev rhev
                        go $ i - 1
                liftIO $ go $ cl - 1
                return csResult
              csvResult <- newTMVarEIO csResult
              clvResult <- newTVarEIO cl
              exitWithResult $ InMemDevCol csvResult clvResult

    withColumnOf' @a other elemOp <|> vecOp

devColOpProc ::
  forall a.
  (Storable a, Eq a, EdhXchg a, Typeable a) =>
  (a -> a -> a) ->
  EdhValue ->
  Edh EdhValue
devColOpProc !op !other =
  withColumnSelfOf @a $ \ !objCol !col -> do
    let exitWithNewClone ::
          forall c' f'.
          ( ManagedColumn c' f' a,
            Typeable (c' a),
            Typeable (f' a),
            Typeable c',
            Typeable f'
          ) =>
          c' a ->
          EIO EdhValue
        exitWithNewClone !colResult =
          liftEdh $
            EdhObject
              <$> mutCloneHostObjectM
                objCol
                objCol
                (someColumn colResult)

        vecOp = liftEIO $ do
          (cs, cl) <- view'column'data col
          liftEdh (fromEdh' @a other) >>= \case
            Nothing -> return edhNA
            Just rhv -> do
              csResult <- do
                (fp, csResult) <- liftIO $ newDeviceArray @a cl
                let p = unsafeForeignPtrToPtr fp
                    go i
                      | i < 0 = return ()
                      | otherwise = do
                        lhev <- array'reader cs i
                        pokeElemOff p i $ op lhev rhv
                        go $ i - 1
                liftIO $ go $ cl - 1
                return csResult
              csvResult <- newTMVarEIO csResult
              clvResult <- newTVarEIO cl
              exitWithNewClone $ InMemDevCol csvResult clvResult

        elemOp ::
          forall c' f'. ManagedColumn c' f' a => Object -> c' a -> Edh EdhValue
        elemOp _ col' = liftEIO $ do
          (cs, cl) <- view'column'data col
          (cs', cl') <- view'column'data col'
          if cl' /= cl
            then
              throwEIO UsageError $
                "column length mistmatch: "
                  <> T.pack (show cl)
                  <> " vs "
                  <> T.pack (show cl')
            else do
              csResult <- do
                (fp, csResult) <- liftIO $ newDeviceArray @a cl
                let p = unsafeForeignPtrToPtr fp
                    go i
                      | i < 0 = return ()
                      | otherwise = do
                        lhev <- array'reader cs i
                        rhev <- array'reader cs' i
                        pokeElemOff p i $ op lhev rhev
                        go $ i - 1
                liftIO $ go $ cl - 1
                return csResult
              csvResult <- newTMVarEIO csResult
              clvResult <- newTVarEIO cl
              exitWithNewClone $ InMemDevCol csvResult clvResult

    withColumnOf' @a other elemOp <|> vecOp

dirColOpProc ::
  forall a.
  (Eq a, EdhXchg a, Typeable a) =>
  (a -> a -> a) ->
  EdhValue ->
  Edh EdhValue
dirColOpProc !op !other =
  withColumnSelfOf @a $ \ !objCol !col -> do
    let exitWithNewClone ::
          forall c' f'.
          ( ManagedColumn c' f' a,
            Typeable (c' a),
            Typeable (f' a),
            Typeable c',
            Typeable f'
          ) =>
          c' a ->
          EIO EdhValue
        exitWithNewClone !colResult =
          liftEdh $
            EdhObject
              <$> mutCloneHostObjectM
                objCol
                objCol
                (someColumn colResult)

        vecOp = liftEIO $ do
          (cs, cl) <- view'column'data col
          liftEdh (fromEdh' @a other) >>= \case
            Nothing -> return edhNA
            Just rhv -> do
              csResult <- do
                (iov, csResult) <- liftIO $ newDirectArray @a cl
                let go i
                      | i < 0 = return ()
                      | otherwise = do
                        lhev <- array'reader cs i
                        MV.unsafeWrite iov i $ op lhev rhv
                        go $ i - 1
                liftIO $ go $ cl - 1
                return csResult
              csvResult <- newTMVarEIO csResult
              clvResult <- newTVarEIO cl
              exitWithNewClone $ InMemDirCol csvResult clvResult

        elemOp ::
          forall c' f'. ManagedColumn c' f' a => Object -> c' a -> Edh EdhValue
        elemOp _ col' = liftEIO $ do
          (cs, cl) <- view'column'data col
          (cs', cl') <- view'column'data col'
          if cl' /= cl
            then
              throwEIO UsageError $
                "column length mistmatch: "
                  <> T.pack (show cl)
                  <> " vs "
                  <> T.pack (show cl')
            else do
              csResult <- do
                (iov, csResult) <- liftIO $ newDirectArray @a cl
                let go i
                      | i < 0 = return ()
                      | otherwise = do
                        lhev <- array'reader cs i
                        rhev <- array'reader cs' i
                        MV.unsafeWrite iov i $ op lhev rhev
                        go $ i - 1
                liftIO $ go $ cl - 1
                return csResult
              csvResult <- newTMVarEIO csResult
              clvResult <- newTVarEIO cl
              exitWithNewClone $ InMemDirCol csvResult clvResult

    withColumnOf' @a other elemOp <|> vecOp

colInpProc ::
  forall a.
  (Eq a, EdhXchg a, Typeable a) =>
  (a -> a -> a) ->
  EdhValue ->
  Edh EdhValue
colInpProc !op !other =
  withColumnSelfOf @a $ \_objCol !col -> do
    let vecOp = do
          (cs, cl) <- liftEIO $ view'column'data col
          fromEdh' @a other >>= \case
            Nothing -> return ()
            Just rhv -> do
              let go i
                    | i < 0 = return ()
                    | otherwise = do
                      lhev <- array'reader cs i
                      array'writer cs i $ op lhev rhv
                      go $ i - 1
              liftIO $ go $ cl - 1

        elemOp ::
          forall c' f'. ManagedColumn c' f' a => Object -> c' a -> Edh ()
        elemOp _ col' = do
          (cs, cl) <- liftEIO $ view'column'data col
          (cs', cl') <- liftEIO $ view'column'data col'
          if cl' /= cl
            then
              throwEdhM UsageError $
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
              liftIO $ go $ cl - 1

    withColumnOf' @a other elemOp <|> vecOp
    EdhObject . edh'scope'that . contextScope . edh'context <$> edhThreadState

dtypeEqProc :: EdhValue -> Edh EdhValue
dtypeEqProc !other = do
  !this <- edh'scope'this . contextScope . edh'context <$> edhThreadState
  case edhUltimate other of
    EdhObject !objOther -> (<|> rtnNeg) $
      withDataType objOther $ \ !dtOther ->
        withDataType this $ \ !dtSelf ->
          return $ EdhBool $ isJust $ dtOther `eqDataType` dtSelf
    _ -> rtnNeg
  where
    rtnNeg = return (EdhBool False)
