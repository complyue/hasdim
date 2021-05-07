module Dim.ColArts where

-- import           Debug.Trace

import Control.Concurrent.STM
import qualified Data.ByteString.Internal as B
import Data.Dynamic
import Data.Lossless.Decimal as D
import Data.Text (Text)
import qualified Data.Text as T
import Dim.Column
import Dim.DataType
import Dim.InMem
import Dim.XCHG
import Foreign hiding (void)
import GHC.Float
import Language.Edh.EHI
import Prelude

vecCmpColumn ::
  DataType ->
  EdhThreadState ->
  (Ordering -> Bool) ->
  Column ->
  EdhValue ->
  (Column -> STM ()) ->
  STM ()
vecCmpColumn !dtYesNo !ets !cmp (Column !col) !v !exit = do
  let !dt = data'type'of'column col
  !cs <- view'column'data col
  !cl <- read'column'length col
  resolveDataComparator ets (data'type'identifier dt) cs $ \ !dtOrd -> do
    let !fa = unsafeSliceFlatArray cs 0 cl
    flat'cmp'vectorized dtOrd ets fa cmp v $ \ !bifa -> do
      !bicsv <- newTVar bifa
      !biclv <- newTVar cl
      exit $ Column $ InMemColumn dtYesNo bicsv biclv

elemCmpColumn ::
  DataType ->
  EdhThreadState ->
  (Ordering -> Bool) ->
  Column ->
  Column ->
  (Column -> STM ()) ->
  STM ()
elemCmpColumn !dtYesNo !ets !cmp (Column !col1) (Column !col2) !exit =
  if data'type'identifier dt1 /= data'type'identifier dt2
    then
      throwEdh ets UsageError $
        "column dtype mismatch: "
          <> data'type'identifier dt1
          <> " vs "
          <> data'type'identifier dt2
    else do
      !cl1 <- read'column'length col1
      !cl2 <- read'column'length col2
      if cl1 /= cl2
        then
          throwEdh ets UsageError $
            "column length mismatch: "
              <> T.pack (show cl1)
              <> " vs "
              <> T.pack (show cl2)
        else do
          !cs1 <- view'column'data col1
          !cs2 <- view'column'data col2
          resolveDataComparator ets (data'type'identifier dt1) cs1 $
            \ !dtOrd -> do
              let !fa1 = unsafeSliceFlatArray cs1 0 cl1
                  !fa2 = unsafeSliceFlatArray cs2 0 cl2
              flat'cmp'element'wise dtOrd ets fa1 cmp fa2 $ \ !bifa -> do
                !bicsv <- newTVar bifa
                !biclv <- newTVar cl1
                exit $ Column $ InMemColumn dtYesNo bicsv biclv
  where
    !dt1 = data'type'of'column col1
    !dt2 = data'type'of'column col2

vecOpColumn ::
  EdhThreadState ->
  (Text -> Dynamic) ->
  Column ->
  EdhValue ->
  STM () ->
  (Column -> STM ()) ->
  STM ()
vecOpColumn !ets !getOp (Column !col) !v !naExit !exit = do
  !cs <- view'column'data col
  !cl <- read'column'length col
  resolveDataOperator' ets (data'type'identifier dt) cs naExit $ \ !dtOp -> do
    let !fa = unsafeSliceFlatArray cs 0 cl
    let !dop = getOp (data'type'identifier dt)
    case fromDynamic dop of
      Just EdhNil -> naExit
      _ -> flat'op'vectorized dtOp ets fa dop v $ \ !bifa -> do
        !bicsv <- newTVar bifa
        !biclv <- newTVar cl
        exit $ Column $ InMemColumn dt bicsv biclv
  where
    !dt = data'type'of'column col

elemOpColumn ::
  EdhThreadState ->
  (Text -> Dynamic) ->
  Column ->
  Column ->
  STM () ->
  (Column -> STM ()) ->
  STM ()
elemOpColumn !ets !getOp (Column !col1) (Column !col2) !naExit !exit =
  if data'type'identifier dt1 /= data'type'identifier dt2
    then
      throwEdh ets UsageError $
        "column dtype mismatch: "
          <> data'type'identifier dt1
          <> " vs "
          <> data'type'identifier dt2
    else do
      !cl1 <- read'column'length col1
      !cl2 <- read'column'length col2
      if cl1 /= cl2
        then
          throwEdh ets UsageError $
            "column length mismatch: "
              <> T.pack (show cl1)
              <> " vs "
              <> T.pack (show cl2)
        else do
          !cs1 <- view'column'data col1
          !cs2 <- view'column'data col2
          resolveDataOperator' ets (data'type'identifier dt1) cs1 naExit $
            \ !dtOp -> do
              let !fa1 = unsafeSliceFlatArray cs1 0 cl1
                  !fa2 = unsafeSliceFlatArray cs2 0 cl2
              let !dop = getOp (data'type'identifier dt1)
              case fromDynamic dop of
                Just EdhNil -> naExit
                _ -> flat'op'element'wise dtOp ets fa1 dop fa2 $ \ !bifa ->
                  do
                    !bicsv <- newTVar bifa
                    !biclv <- newTVar cl1
                    exit $ Column $ InMemColumn dt1 bicsv biclv
  where
    !dt1 = data'type'of'column col1
    !dt2 = data'type'of'column col2

vecInpColumn ::
  EdhThreadState ->
  (Text -> Dynamic) ->
  Column ->
  EdhValue ->
  STM () ->
  STM () ->
  STM ()
vecInpColumn !ets !getOp (Column !col) !v !naExit !exit = do
  !cl <- read'column'length col
  !cs <- view'column'data col
  resolveDataOperator' ets (data'type'identifier dt) cs naExit $ \ !dtOp -> do
    let !fa = unsafeSliceFlatArray cs 0 cl
    let !dop = getOp (data'type'identifier dt)
    case fromDynamic dop of
      Just EdhNil -> naExit
      _ -> flat'inp'vectorized dtOp ets fa dop v exit
  where
    !dt = data'type'of'column col

vecInpSliceColumn ::
  EdhThreadState ->
  (Int, Int, Int) ->
  (Text -> Dynamic) ->
  Column ->
  EdhValue ->
  STM () ->
  STM () ->
  STM ()
vecInpSliceColumn !ets !slice !getOp (Column !col) !v !naExit !exit = do
  !cl <- read'column'length col
  !cs <- view'column'data col
  resolveDataOperator' ets (data'type'identifier dt) cs naExit $ \ !dtOp -> do
    let !fa = unsafeSliceFlatArray cs 0 cl
    let !dop = getOp (data'type'identifier dt)
    case fromDynamic dop of
      Just EdhNil -> naExit
      _ -> flat'inp'vectorized'slice dtOp ets slice fa dop v exit
  where
    !dt = data'type'of'column col

vecInpMaskedColumn ::
  EdhThreadState ->
  Column ->
  (Text -> Dynamic) ->
  Column ->
  EdhValue ->
  STM () ->
  STM () ->
  STM ()
vecInpMaskedColumn
  !ets
  (Column !colMask)
  !getOp
  (Column !col)
  !v
  !naExit
  !exit = do
    !cl <- read'column'length col
    !cs <- view'column'data col
    resolveDataOperator' ets (data'type'identifier dt) cs naExit $
      \ !dtOp -> do
        let !fa = unsafeSliceFlatArray cs 0 cl
        let !dop = getOp (data'type'identifier dt)
        case fromDynamic dop of
          Just EdhNil -> naExit
          _ -> do
            !mcl <- read'column'length colMask
            if mcl /= cl
              then
                throwEdh ets UsageError $
                  "index length mismatch: "
                    <> T.pack (show mcl)
                    <> " vs "
                    <> T.pack (show cl)
              else do
                !mcs <- view'column'data colMask
                let !ma = unsafeSliceFlatArray mcs 0 mcl
                flat'inp'vectorized'masked dtOp ets ma fa dop v exit
    where
      !dt = data'type'of'column col

vecInpFancyColumn ::
  EdhThreadState ->
  Column ->
  (Text -> Dynamic) ->
  Column ->
  EdhValue ->
  STM () ->
  STM () ->
  STM ()
vecInpFancyColumn !ets (Column !colIdx) !getOp (Column !col) !v !naExit !exit =
  do
    !cl <- read'column'length col
    !cs <- view'column'data col
    resolveDataOperator' ets (data'type'identifier dt) cs naExit $ \ !dtOp -> do
      let !fa = unsafeSliceFlatArray cs 0 cl
      let !dop = getOp (data'type'identifier dt)
      case fromDynamic dop of
        Just EdhNil -> naExit
        _ -> do
          !icl <- read'column'length colIdx
          !ics <- view'column'data colIdx
          let !ia = unsafeSliceFlatArray ics 0 icl
          flat'inp'vectorized'fancy dtOp ets ia fa dop v exit
  where
    !dt = data'type'of'column col

elemInpColumn ::
  EdhThreadState ->
  (Text -> Dynamic) ->
  Column ->
  Column ->
  STM () ->
  STM () ->
  STM ()
elemInpColumn !ets !getOp (Column !col1) (Column !col2) !naExit !exit =
  if data'type'identifier dt1 /= data'type'identifier dt2
    then
      throwEdh ets UsageError $
        "column dtype mismatch: "
          <> data'type'identifier dt1
          <> " vs "
          <> data'type'identifier dt2
    else do
      !cl1 <- read'column'length col1
      !cl2 <- read'column'length col2
      if cl1 /= cl2
        then
          throwEdh ets UsageError $
            "column length mismatch: "
              <> T.pack (show cl1)
              <> " vs "
              <> T.pack (show cl2)
        else do
          !cs1 <- view'column'data col1
          !cs2 <- view'column'data col2
          resolveDataOperator' ets (data'type'identifier dt1) cs1 naExit $
            \ !dtOp -> do
              let !fa1 = unsafeSliceFlatArray cs1 0 cl1
                  !fa2 = unsafeSliceFlatArray cs2 0 cl2
              let !dop = getOp (data'type'identifier dt1)
              case fromDynamic dop of
                Just EdhNil -> naExit
                _ -> flat'inp'element'wise dtOp ets fa1 dop fa2 exit
  where
    !dt1 = data'type'of'column col1
    !dt2 = data'type'of'column col2

elemInpSliceColumn ::
  EdhThreadState ->
  (Int, Int, Int) ->
  (Text -> Dynamic) ->
  Column ->
  Column ->
  STM () ->
  STM () ->
  STM ()
elemInpSliceColumn
  !ets
  !slice
  !getOp
  (Column !col1)
  (Column !col2)
  !naExit
  !exit =
    if data'type'identifier dt1 /= data'type'identifier dt2
      then
        throwEdh ets UsageError $
          "column dtype mismatch: "
            <> data'type'identifier dt1
            <> " vs "
            <> data'type'identifier dt2
      else do
        !cl1 <- read'column'length col1
        !cl2 <- read'column'length col2
        !cs1 <- view'column'data col1
        !cs2 <- view'column'data col2
        resolveDataOperator' ets (data'type'identifier dt1) cs1 naExit $
          \ !dtOp -> do
            let !fa1 = unsafeSliceFlatArray cs1 0 cl1
                !fa2 = unsafeSliceFlatArray cs2 0 cl2
            let !dop = getOp (data'type'identifier dt1)
            case fromDynamic dop of
              Just EdhNil -> naExit
              _ -> flat'inp'element'wise'slice dtOp ets slice fa1 dop fa2 exit
    where
      !dt1 = data'type'of'column col1
      !dt2 = data'type'of'column col2

elemInpMaskedColumn ::
  EdhThreadState ->
  Column ->
  (Text -> Dynamic) ->
  Column ->
  Column ->
  STM () ->
  STM () ->
  STM ()
elemInpMaskedColumn
  !ets
  (Column !colMask)
  !getOp
  (Column !col1)
  (Column !col2)
  !naExit
  !exit =
    if data'type'identifier dt1 /= data'type'identifier dt2
      then
        throwEdh ets UsageError $
          "column dtype mismatch: "
            <> data'type'identifier dt1
            <> " vs "
            <> data'type'identifier dt2
      else do
        !cl1 <- read'column'length col1
        !cl2 <- read'column'length col2
        if cl1 /= cl2
          then
            throwEdh ets UsageError $
              "column length mismatch: "
                <> T.pack (show cl1)
                <> " vs "
                <> T.pack (show cl2)
          else do
            !mcl <- read'column'length colMask
            !mcs <- view'column'data colMask
            !cs1 <- view'column'data col1
            !cs2 <- view'column'data col2
            resolveDataOperator' ets (data'type'identifier dt1) cs1 naExit $
              \ !dtOp -> do
                let !ma = unsafeSliceFlatArray mcs 0 mcl
                    !fa1 = unsafeSliceFlatArray cs1 0 cl1
                    !fa2 = unsafeSliceFlatArray cs2 0 cl2
                let !dop = getOp (data'type'identifier dt1)
                case fromDynamic dop of
                  Just EdhNil -> naExit
                  _ ->
                    flat'inp'element'wise'masked dtOp ets ma fa1 dop fa2 exit
    where
      !dt1 = data'type'of'column col1
      !dt2 = data'type'of'column col2

elemInpFancyColumn ::
  EdhThreadState ->
  Column ->
  (Text -> Dynamic) ->
  Column ->
  Column ->
  STM () ->
  STM () ->
  STM ()
elemInpFancyColumn
  !ets
  (Column !colIdx)
  !getOp
  (Column !col1)
  (Column !col2)
  !naExit
  !exit =
    if data'type'identifier dt1 /= data'type'identifier dt2
      then
        throwEdh ets UsageError $
          "column dtype mismatch: "
            <> data'type'identifier dt1
            <> " vs "
            <> data'type'identifier dt2
      else do
        !cl1 <- read'column'length col1
        !cl2 <- read'column'length col2
        if cl1 /= cl2
          then
            throwEdh ets UsageError $
              "column length mismatch: "
                <> T.pack (show cl1)
                <> " vs "
                <> T.pack (show cl2)
          else do
            !icl <- read'column'length colIdx
            !ics <- view'column'data colIdx
            !cs1 <- view'column'data col1
            !cs2 <- view'column'data col2
            resolveDataOperator' ets (data'type'identifier dt1) cs1 naExit $
              \ !dtOp -> do
                let !ia = unsafeSliceFlatArray ics 0 icl
                    !fa1 = unsafeSliceFlatArray cs1 0 cl1
                    !fa2 = unsafeSliceFlatArray cs2 0 cl2
                let !dop = getOp (data'type'identifier dt1)
                case fromDynamic dop of
                  Just EdhNil -> naExit
                  _ -> flat'inp'element'wise'fancy dtOp ets ia fa1 dop fa2 exit
    where
      !dt1 = data'type'of'column col1
      !dt2 = data'type'of'column col2

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

createColumnClass :: Object -> Scope -> STM Object
createColumnClass !defaultDt !clsOuterScope =
  mkHostClass clsOuterScope "Column" (allocEdhObj columnAllocator) [] $
    \ !clsScope -> do
      !mths <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc clsScope vc nm hp
            | (nm, vc, hp) <-
                [ ("__cap__", EdhMethod, wrapHostProc colCapProc),
                  ("__grow__", EdhMethod, wrapHostProc colGrowProc),
                  ("__len__", EdhMethod, wrapHostProc colLenProc),
                  ("__mark__", EdhMethod, wrapHostProc colMarkLenProc),
                  ("([])", EdhMethod, wrapHostProc colIdxReadProc),
                  ("([=])", EdhMethod, wrapHostProc colIdxWriteProc),
                  ("__blob__", EdhMethod, wrapHostProc colBlobProc),
                  ("__repr__", EdhMethod, wrapHostProc colReprProc),
                  ("__show__", EdhMethod, wrapHostProc colShowProc),
                  ("__desc__", EdhMethod, wrapHostProc colDescProc),
                  ("__json__", EdhMethod, wrapHostProc colJsonProc),
                  ( "==",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc $ \case
                        EQ -> True
                        _ -> False
                  ),
                  ( "(==.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc $ \case
                        EQ -> True
                        _ -> False
                  ),
                  ( "(!=)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc $ \case
                        EQ -> False
                        _ -> True
                  ),
                  ( "(!=.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc $ \case
                        EQ -> False
                        _ -> True
                  ),
                  ( "(>=)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc $ \case
                        GT -> True
                        EQ -> True
                        _ -> False
                  ),
                  ( "(<=)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc $ \case
                        LT -> True
                        EQ -> True
                        _ -> False
                  ),
                  ( "(<)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc $ \case
                        LT -> True
                        _ -> False
                  ),
                  ( "(>)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc $ \case
                        GT -> True
                        _ -> False
                  ),
                  ( "(>=.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc $ \case
                        LT -> True
                        EQ -> True
                        _ -> False
                  ),
                  ( "(<=.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc $ \case
                        GT -> True
                        EQ -> True
                        _ -> False
                  ),
                  ( "(<.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc $ \case
                        GT -> True
                        _ -> False
                  ),
                  ( "(>.)",
                    EdhMethod,
                    wrapHostProc $
                      colCmpProc $ \case
                        LT -> True
                        _ -> False
                  ),
                  ("(&&)", EdhMethod, wrapHostProc $ colOpProc bitAndOp),
                  ("(&&.)", EdhMethod, wrapHostProc $ colOpProc bitAndOp),
                  ("(||)", EdhMethod, wrapHostProc $ colOpProc bitOrOp),
                  ("(||.)", EdhMethod, wrapHostProc $ colOpProc bitOrOp),
                  ("(&&=)", EdhMethod, wrapHostProc $ colInpProc bitAndOp),
                  ("(||=)", EdhMethod, wrapHostProc $ colInpProc bitOrOp),
                  ("(+)", EdhMethod, wrapHostProc $ colOpProc addOp),
                  ("(+.)", EdhMethod, wrapHostProc $ colOpProc addToOp),
                  ("(+=)", EdhMethod, wrapHostProc $ colInpProc addOp),
                  ("(-)", EdhMethod, wrapHostProc $ colOpProc subtractOp),
                  ("(-.)", EdhMethod, wrapHostProc $ colOpProc subtFromOp),
                  ("(-=)", EdhMethod, wrapHostProc $ colInpProc subtractOp),
                  ("(*)", EdhMethod, wrapHostProc $ colOpProc mulOp),
                  ("(*.)", EdhMethod, wrapHostProc $ colOpProc mulOp),
                  ("(*=)", EdhMethod, wrapHostProc $ colInpProc mulOp),
                  ("(/)", EdhMethod, wrapHostProc $ colOpProc divOp),
                  ("(/.)", EdhMethod, wrapHostProc $ colOpProc divByOp),
                  ("(/=)", EdhMethod, wrapHostProc $ colInpProc divOp),
                  ("(//)", EdhMethod, wrapHostProc $ colOpProc divIntOp),
                  ("(//.)", EdhMethod, wrapHostProc $ colOpProc divIntByOp),
                  ("(//=)", EdhMethod, wrapHostProc $ colInpProc divIntOp),
                  ("(**)", EdhMethod, wrapHostProc $ colOpProc powOp),
                  ("(**.)", EdhMethod, wrapHostProc $ colOpProc powToOp),
                  ("(**=)", EdhMethod, wrapHostProc $ colInpProc powOp)
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
        | ctorCap <= 0 =
          throwEdh etsCtor UsageError $
            "column capacity should be a positive interger, not "
              <> T.pack (show ctorCap)
        | ctorLen < 0 =
          throwEdh etsCtor UsageError $
            "column length should be zero or a positive integer, not "
              <> T.pack (show ctorLen)
        | otherwise =
          castObjectStore dto >>= \case
            Nothing -> throwEdh etsCtor UsageError "invalid dtype"
            Just (_, !dt) ->
              runEdhTx etsCtor $
                createInMemColumn dt ctorCap ctorLen $
                  ctorExit Nothing . HostStore . toDyn

    dtYesNo = makeDeviceDataType @YesNo "yesno"

    colGrowProc :: "newCap" !: Int -> EdhHostProc
    colGrowProc (mandatoryArg -> !newCap) !exit !ets =
      if newCap < 0
        then
          throwEdh ets UsageError $
            "invalid newCap: " <> T.pack (show newCap)
        else withThisHostObj ets $ \(Column !col) ->
          runEdhTx ets $
            grow'column'capacity col newCap $
              const $
                exitEdh ets exit $
                  EdhObject $ edh'scope'that $ contextScope $ edh'context ets

    colCapProc :: EdhHostProc
    colCapProc !exit !ets = withThisHostObj ets $ \ !col ->
      columnCapacity col
        >>= \ !cap -> exitEdh ets exit $ EdhDecimal $ fromIntegral cap

    colLenProc :: EdhHostProc
    colLenProc !exit !ets = withThisHostObj ets $ \(Column !col) ->
      read'column'length col
        >>= \ !len -> exitEdh ets exit $ EdhDecimal $ fromIntegral len

    colMarkLenProc :: "newLen" !: Int -> EdhHostProc
    colMarkLenProc (mandatoryArg -> !newLen) !exit !ets =
      withThisHostObj ets $ \(Column !col) ->
        runEdhTx ets $ mark'column'length col newLen $ exitEdh ets exit nil

    colDtypeProc :: EdhHostProc
    colDtypeProc !exit !ets = withThisHostObj ets $ \(Column !col) ->
      exitEdh ets exit $
        EdhString $ data'type'identifier $ data'type'of'column col

    colBlobProc :: EdhHostProc
    colBlobProc !exit !ets =
      withThisHostObj' ets (exitEdh ets exit $ EdhString "<bogus-Column>") $
        \(Column !col) -> case data'type'proxy $ data'type'of'column col of
          DeviceDataType _ !item'size _item'align -> do
            !cs <- view'column'data col
            !cl <- read'column'length col
            case cs of
              DeviceArray _cap !fp ->
                exitEdh ets exit $
                  EdhBlob $
                    B.fromForeignPtr
                      (castForeignPtr fp)
                      0
                      (cl * item'size)
              _ -> exitEdh ets exit edhNA
          _ -> exitEdh ets exit edhNA

    colReprProc :: EdhHostProc
    colReprProc !exit !ets =
      withThisHostObj' ets (exitEdh ets exit $ EdhString "<bogus-Column>") $
        \(Column !col) -> do
          let !dt = data'type'of'column col
          !cs <- view'column'data col
          !cl <- read'column'length col
          exitEdh ets exit $
            EdhString $
              "Column( capacity="
                <> T.pack (show $ flatArrayCapacity cs)
                <> ", length="
                <> T.pack (show cl)
                <> ", dtype="
                -- assuming the identifier is available as attr
                <> data'type'identifier dt
                <> ")"

    colShowProc :: EdhHostProc
    colShowProc !exit !ets = withThisHostObj ets $ \(Column !col) -> do
      let !dt = data'type'of'column col
      !cs <- view'column'data col
      !cl <- read'column'length col
      showData cl $ flat'array'read dt ets cs
      where
        !thisCol = edh'scope'this $ contextScope $ edh'context ets

        exitWithDetails :: Text -> STM ()
        exitWithDetails !details = edhValueRepr ets (EdhObject thisCol) $
          \ !repr -> exitEdh ets exit $ EdhString $ repr <> "\n" <> details

        showData :: Int -> (Int -> (EdhValue -> STM ()) -> STM ()) -> STM ()
        showData !len !readElem = go 0 [] 0 ""
          where
            go :: Int -> [Text] -> Int -> Text -> STM ()
            -- TODO don't generate all lines for large columns
            go !i !cumLines !lineIdx !line
              | i >= len =
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
            go !i !cumLines !lineIdx !line = readElem i $ \ !elemVal ->
              edhValueRepr ets elemVal $ \ !elemRepr ->
                let !tentLine = line <> elemRepr <> ", "
                 in if T.length tentLine > 79 -- todo make this tunable ?
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

    colJsonProc :: EdhHostProc
    colJsonProc !exit !ets = withThisHostObj ets $ \(Column !col) -> do
      let !dt = data'type'of'column col
      !cs <- view'column'data col
      !cl <- read'column'length col
      if cl <= 0
        then exitEdh ets exit $ EdhString "[]"
        else cvt2Json cl $ flat'array'read dt ets cs
      where
        cvt2Json :: Int -> (Int -> (EdhValue -> STM ()) -> STM ()) -> STM ()
        cvt2Json !len !readElem = go (len -1) []
          where
            go :: Int -> [Text] -> STM ()
            go !i !elemJsonStrs
              | i < 0 =
                exitEdh ets exit $
                  EdhString $ "[" <> T.intercalate "," elemJsonStrs <> "]"
              | otherwise = readElem i $ \ !elemVal ->
                edhValueJson ets elemVal $ \ !elemJsonStr ->
                  go (i -1) $ elemJsonStr : elemJsonStrs

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
      withThisHostObj ets $ \col'@(Column !col) ->
        castObjectStore' idxVal >>= \case
          Just (_, idxCol'@(Column !idxCol)) ->
            case data'type'identifier $ data'type'of'column idxCol of
              "yesno" ->
                -- yesno index
                extractColumnBool ets thatCol idxCol' (exitEdh ets exit edhNA) $
                  \_clNew !newColObj -> exitEdh ets exit $ EdhObject newColObj
              "intp" ->
                -- fancy index
                extractColumnFancy
                  ets
                  thatCol
                  idxCol'
                  (exitEdh ets exit edhNA)
                  (exitEdh ets exit . EdhObject)
              !badDti ->
                throwEdh ets UsageError $
                  "invalid dtype="
                    <> badDti
                    <> " for a column as an index to another column"
          Nothing -> parseEdhIndex ets idxVal $ \case
            Left !err -> throwEdh ets UsageError err
            Right (EdhIndex !i) ->
              unsafeReadColumnCell ets col' i $ exitEdh ets exit
            Right EdhAny -> exitEdh ets exit $ EdhObject thatCol
            Right EdhAll -> exitEdh ets exit $ EdhObject thatCol
            Right (EdhSlice !start !stop !step) -> do
              !cl <- read'column'length col
              edhRegulateSlice ets cl (start, stop, step) $
                \(!iStart, !iStop, !iStep) ->
                  sliceColumn ets thatCol iStart iStop iStep $
                    \_ccNew _clNew !newColObj ->
                      exitEdh ets exit $ EdhObject newColObj
      where
        !thatCol = edh'scope'that $ contextScope $ edh'context ets

    colIdxWriteProc :: EdhValue -> EdhValue -> EdhHostProc
    colIdxWriteProc !idxVal !other !exit !ets =
      withThisHostObj ets $ \ !col -> idxAssignColumn col idxVal other exit ets

    colCmpProc :: (Ordering -> Bool) -> EdhValue -> EdhHostProc
    colCmpProc !cmp !other !exit !ets = withThisHostObj ets $ \ !col ->
      let !otherVal = edhUltimate other
       in castObjectStore' otherVal >>= \case
            Just (_, colOther@Column {}) ->
              elemCmpColumn dtYesNo ets cmp col colOther exitWithResult
            _ -> vecCmpColumn dtYesNo ets cmp col otherVal exitWithResult
      where
        !thisCol = edh'scope'this $ contextScope $ edh'context ets
        exitWithResult !colResult =
          edhCreateHostObj (edh'obj'class thisCol) colResult
            >>= exitEdh ets exit
              . EdhObject

    colOpProc :: (Text -> Dynamic) -> EdhValue -> EdhHostProc
    colOpProc !getOp !other !exit !ets = withThisHostObj ets $ \ !col ->
      let !otherVal = edhUltimate other
       in castObjectStore' otherVal >>= \case
            Just (_, colOther@Column {}) ->
              elemOpColumn
                ets
                getOp
                col
                colOther
                (exitEdh ets exit edhNA)
                exitWithNewClone
            _ ->
              vecOpColumn
                ets
                getOp
                col
                otherVal
                (exitEdh ets exit edhNA)
                exitWithNewClone
      where
        !thisCol = edh'scope'this $ contextScope $ edh'context ets
        !thatCol = edh'scope'that $ contextScope $ edh'context ets
        exitWithNewClone !colResult =
          edhCloneHostObj ets thisCol thatCol colResult $
            \ !newColObj -> exitEdh ets exit $ EdhObject newColObj

    colInpProc :: (Text -> Dynamic) -> EdhValue -> EdhHostProc
    colInpProc !getOp !other !exit !ets = withThisHostObj ets $ \ !col ->
      let !otherVal = edhUltimate other
       in castObjectStore' otherVal >>= \case
            Just (_, colOther@Column {}) ->
              elemInpColumn ets getOp col colOther (exitEdh ets exit edhNA) $
                exitEdh ets exit $
                  EdhObject thatCol
            _ ->
              vecInpColumn ets getOp col otherVal (exitEdh ets exit edhNA) $
                exitEdh ets exit $
                  EdhObject thatCol
      where
        !thatCol = edh'scope'that $ contextScope $ edh'context ets

assignOp :: Text -> Dynamic
assignOp = \case
  "float64" -> toDyn ((\_x !y -> y) :: Double -> Double -> Double)
  "float32" -> toDyn ((\_x !y -> y) :: Float -> Float -> Float)
  "int64" -> toDyn ((\_x !y -> y) :: Int64 -> Int64 -> Int64)
  "int32" -> toDyn ((\_x !y -> y) :: Int32 -> Int32 -> Int32)
  "int8" -> toDyn ((\_x !y -> y) :: Int8 -> Int8 -> Int8)
  "byte" -> toDyn ((\_x !y -> y) :: Word8 -> Word8 -> Word8)
  "intp" -> toDyn ((\_x !y -> y) :: Int -> Int -> Int)
  "yesno" -> toDyn ((\_x !y -> y) :: YesNo -> YesNo -> YesNo)
  "decimal" -> toDyn ((\_x !y -> y) :: D.Decimal -> D.Decimal -> D.Decimal)
  "box" ->
    let edhOp :: EdhValue -> EdhValue -> EdhHostProc
        edhOp _x !y !exit !ets = exitEdh ets exit y
     in toDyn edhOp
  _ -> toDyn nil -- means not applicable here

bitAndOp :: Text -> Dynamic
bitAndOp = \case
  -- "float64" -> toDyn ((.&.) :: Double -> Double -> Double)
  -- "float32" -> toDyn ((.&.) :: Float -> Float -> Float)
  "int64" -> toDyn ((.&.) :: Int64 -> Int64 -> Int64)
  "int32" -> toDyn ((.&.) :: Int32 -> Int32 -> Int32)
  "int8" -> toDyn ((.&.) :: Int8 -> Int8 -> Int8)
  "byte" -> toDyn ((.&.) :: Word8 -> Word8 -> Word8)
  "intp" -> toDyn ((.&.) :: Int -> Int -> Int)
  "yesno" -> toDyn ((.&.) :: YesNo -> YesNo -> YesNo)
  -- "decimal" -> toDyn ((.&.) :: D.Decimal -> D.Decimal -> D.Decimal)
  "box" ->
    let edhOp :: EdhValue -> EdhValue -> EdhHostProc
        edhOp !x !y =
          evalInfix "&&" (LitExpr $ ValueLiteral x) (LitExpr $ ValueLiteral y)
     in toDyn edhOp
  _ -> toDyn nil -- means not applicable here

bitOrOp :: Text -> Dynamic
bitOrOp = \case
  -- "float64" -> toDyn ((.|.) :: Double -> Double -> Double)
  -- "float32" -> toDyn ((.|.) :: Float -> Float -> Float)
  "int64" -> toDyn ((.|.) :: Int64 -> Int64 -> Int64)
  "int32" -> toDyn ((.|.) :: Int32 -> Int32 -> Int32)
  "int8" -> toDyn ((.|.) :: Int8 -> Int8 -> Int8)
  "byte" -> toDyn ((.|.) :: Word8 -> Word8 -> Word8)
  "intp" -> toDyn ((.|.) :: Int -> Int -> Int)
  "yesno" -> toDyn ((.|.) :: YesNo -> YesNo -> YesNo)
  -- "decimal" -> toDyn ((.|.) :: D.Decimal -> D.Decimal -> D.Decimal)
  "box" ->
    let edhOp :: EdhValue -> EdhValue -> EdhHostProc
        edhOp !x !y =
          evalInfix "||" (LitExpr $ ValueLiteral x) (LitExpr $ ValueLiteral y)
     in toDyn edhOp
  _ -> toDyn nil -- means not applicable here

addOp :: Text -> Dynamic
addOp = \case
  "float64" -> toDyn ((+) :: Double -> Double -> Double)
  "float32" -> toDyn ((+) :: Float -> Float -> Float)
  "int64" -> toDyn ((+) :: Int64 -> Int64 -> Int64)
  "int32" -> toDyn ((+) :: Int32 -> Int32 -> Int32)
  "int8" -> toDyn ((+) :: Int8 -> Int8 -> Int8)
  "byte" -> toDyn ((+) :: Word8 -> Word8 -> Word8)
  "intp" -> toDyn ((+) :: Int -> Int -> Int)
  "decimal" -> toDyn ((+) :: D.Decimal -> D.Decimal -> D.Decimal)
  "box" ->
    let edhOp :: EdhValue -> EdhValue -> EdhHostProc
        edhOp !x !y =
          evalInfix "+" (LitExpr $ ValueLiteral x) (LitExpr $ ValueLiteral y)
     in toDyn edhOp
  _ -> toDyn nil -- means not applicable here

addToOp :: Text -> Dynamic
addToOp = \case
  "float64" -> toDyn ((+) :: Double -> Double -> Double)
  "float32" -> toDyn ((+) :: Float -> Float -> Float)
  "int64" -> toDyn ((+) :: Int64 -> Int64 -> Int64)
  "int32" -> toDyn ((+) :: Int32 -> Int32 -> Int32)
  "int8" -> toDyn ((+) :: Int8 -> Int8 -> Int8)
  "byte" -> toDyn ((+) :: Word8 -> Word8 -> Word8)
  "intp" -> toDyn ((+) :: Int -> Int -> Int)
  "decimal" -> toDyn ((+) :: D.Decimal -> D.Decimal -> D.Decimal)
  "box" ->
    let edhOp :: EdhValue -> EdhValue -> EdhHostProc
        edhOp !x !y =
          evalInfix "+" (LitExpr $ ValueLiteral y) (LitExpr $ ValueLiteral x)
     in toDyn edhOp
  _ -> toDyn nil -- means not applicable here

subtractOp :: Text -> Dynamic
subtractOp = \case
  "float64" -> toDyn ((-) :: Double -> Double -> Double)
  "float32" -> toDyn ((-) :: Float -> Float -> Float)
  "int64" -> toDyn ((-) :: Int64 -> Int64 -> Int64)
  "int32" -> toDyn ((-) :: Int32 -> Int32 -> Int32)
  "int8" -> toDyn ((-) :: Int8 -> Int8 -> Int8)
  "byte" -> toDyn ((-) :: Word8 -> Word8 -> Word8)
  "intp" -> toDyn ((-) :: Int -> Int -> Int)
  "decimal" -> toDyn ((-) :: D.Decimal -> D.Decimal -> D.Decimal)
  "box" ->
    let edhOp :: EdhValue -> EdhValue -> EdhHostProc
        edhOp !x !y =
          evalInfix "-" (LitExpr $ ValueLiteral x) (LitExpr $ ValueLiteral y)
     in toDyn edhOp
  _ -> toDyn nil -- means not applicable here

subtFromOp :: Text -> Dynamic
subtFromOp = \case
  "float64" -> toDyn ((\ !x !y -> y - x) :: Double -> Double -> Double)
  "float32" -> toDyn ((\ !x !y -> y - x) :: Float -> Float -> Float)
  "int64" -> toDyn ((\ !x !y -> y - x) :: Int64 -> Int64 -> Int64)
  "int32" -> toDyn ((\ !x !y -> y - x) :: Int32 -> Int32 -> Int32)
  "int8" -> toDyn ((\ !x !y -> y - x) :: Int8 -> Int8 -> Int8)
  "byte" -> toDyn ((\ !x !y -> y - x) :: Word8 -> Word8 -> Word8)
  "intp" -> toDyn ((\ !x !y -> y - x) :: Int -> Int -> Int)
  "decimal" ->
    toDyn ((\ !x !y -> y - x) :: D.Decimal -> D.Decimal -> D.Decimal)
  "box" ->
    let edhOp :: EdhValue -> EdhValue -> EdhHostProc
        edhOp !x !y =
          evalInfix "-" (LitExpr $ ValueLiteral y) (LitExpr $ ValueLiteral x)
     in toDyn edhOp
  _ -> toDyn nil -- means not applicable here

mulOp :: Text -> Dynamic
mulOp = \case
  "float64" -> toDyn ((*) :: Double -> Double -> Double)
  "float32" -> toDyn ((*) :: Float -> Float -> Float)
  "int64" -> toDyn ((*) :: Int64 -> Int64 -> Int64)
  "int32" -> toDyn ((*) :: Int32 -> Int32 -> Int32)
  "int8" -> toDyn ((*) :: Int8 -> Int8 -> Int8)
  "byte" -> toDyn ((*) :: Word8 -> Word8 -> Word8)
  "intp" -> toDyn ((*) :: Int -> Int -> Int)
  "decimal" -> toDyn ((*) :: D.Decimal -> D.Decimal -> D.Decimal)
  "box" ->
    let edhOp :: EdhValue -> EdhValue -> EdhHostProc
        edhOp !x !y =
          evalInfix "*" (LitExpr $ ValueLiteral x) (LitExpr $ ValueLiteral y)
     in toDyn edhOp
  _ -> toDyn nil -- means not applicable here

divOp :: Text -> Dynamic
divOp = \case
  "float64" -> toDyn ((/) :: Double -> Double -> Double)
  "float32" -> toDyn ((/) :: Float -> Float -> Float)
  "int64" -> toDyn (div :: Int64 -> Int64 -> Int64)
  "int32" -> toDyn (div :: Int32 -> Int32 -> Int32)
  "int8" -> toDyn (div :: Int8 -> Int8 -> Int8)
  "byte" -> toDyn (div :: Word8 -> Word8 -> Word8)
  "intp" -> toDyn (div :: Int -> Int -> Int)
  "decimal" -> toDyn (D.divDecimal :: D.Decimal -> D.Decimal -> D.Decimal)
  "box" ->
    let edhOp :: EdhValue -> EdhValue -> EdhHostProc
        edhOp !x !y =
          evalInfix "/" (LitExpr $ ValueLiteral x) (LitExpr $ ValueLiteral y)
     in toDyn edhOp
  _ -> toDyn nil -- means not applicable here

divByOp :: Text -> Dynamic
divByOp = \case
  "float64" -> toDyn ((\ !x !y -> y / x) :: Double -> Double -> Double)
  "float32" -> toDyn ((\ !x !y -> y / x) :: Float -> Float -> Float)
  "int64" -> toDyn ((\ !x !y -> div y x) :: Int64 -> Int64 -> Int64)
  "int32" -> toDyn ((\ !x !y -> div y x) :: Int32 -> Int32 -> Int32)
  "int8" -> toDyn ((\ !x !y -> div y x) :: Int8 -> Int8 -> Int8)
  "byte" -> toDyn ((\ !x !y -> div y x) :: Word8 -> Word8 -> Word8)
  "intp" -> toDyn ((\ !x !y -> div y x) :: Int -> Int -> Int)
  "decimal" ->
    toDyn
      ((\ !x !y -> D.divDecimal y x) :: D.Decimal -> D.Decimal -> D.Decimal)
  "box" ->
    let edhOp :: EdhValue -> EdhValue -> EdhHostProc
        edhOp !x !y =
          evalInfix "/" (LitExpr $ ValueLiteral y) (LitExpr $ ValueLiteral x)
     in toDyn edhOp
  _ -> toDyn nil -- means not applicable here

divIntOp :: Text -> Dynamic
divIntOp = \case
  -- TODO reason about this:
  -- https://stackoverflow.com/questions/38588815/rounding-errors-in-python-floor-division
  "float64" ->
    toDyn
      ((\ !x !y -> fromInteger $ floor $ x / y) :: Double -> Double -> Double)
  "float32" ->
    toDyn
      ((\ !x !y -> fromInteger $ floor $ x / y) :: Float -> Float -> Float)
  "int64" -> toDyn (div :: Int64 -> Int64 -> Int64)
  "int32" -> toDyn (div :: Int32 -> Int32 -> Int32)
  "int8" -> toDyn (div :: Int8 -> Int8 -> Int8)
  "byte" -> toDyn (div :: Word8 -> Word8 -> Word8)
  "intp" -> toDyn (div :: Int -> Int -> Int)
  "decimal" -> toDyn (D.divIntDecimal :: D.Decimal -> D.Decimal -> D.Decimal)
  "box" ->
    let edhOp :: EdhValue -> EdhValue -> EdhHostProc
        edhOp !x !y =
          evalInfix "//" (LitExpr $ ValueLiteral x) (LitExpr $ ValueLiteral y)
     in toDyn edhOp
  _ -> toDyn nil -- means not applicable here

divIntByOp :: Text -> Dynamic
divIntByOp = \case
  "float64" ->
    toDyn
      ((\ !x !y -> fromInteger $ floor $ y / x) :: Double -> Double -> Double)
  "float32" ->
    toDyn
      ((\ !x !y -> fromInteger $ floor $ y / x) :: Float -> Float -> Float)
  "int64" -> toDyn ((\ !x !y -> div y x) :: Int64 -> Int64 -> Int64)
  "int32" -> toDyn ((\ !x !y -> div y x) :: Int32 -> Int32 -> Int32)
  "int8" -> toDyn ((\ !x !y -> div y x) :: Int8 -> Int8 -> Int8)
  "byte" -> toDyn ((\ !x !y -> div y x) :: Word8 -> Word8 -> Word8)
  "intp" -> toDyn ((\ !x !y -> div y x) :: Int -> Int -> Int)
  "decimal" ->
    toDyn
      ((\ !x !y -> D.divIntDecimal y x) :: D.Decimal -> D.Decimal -> D.Decimal)
  "box" ->
    let edhOp :: EdhValue -> EdhValue -> EdhHostProc
        edhOp !x !y =
          evalInfix "//" (LitExpr $ ValueLiteral y) (LitExpr $ ValueLiteral x)
     in toDyn edhOp
  _ -> toDyn nil -- means not applicable here

powOp :: Text -> Dynamic
powOp = \case
  "float64" -> toDyn powerDouble
  "float32" -> toDyn powerFloat
  "int64" -> toDyn ((^) :: Int64 -> Int64 -> Int64)
  "int32" -> toDyn ((^) :: Int32 -> Int32 -> Int32)
  "int8" -> toDyn ((^) :: Int8 -> Int8 -> Int8)
  "byte" -> toDyn ((^) :: Word8 -> Word8 -> Word8)
  "intp" -> toDyn ((^) :: Int -> Int -> Int)
  "decimal" -> toDyn D.powerDecimal
  "box" ->
    let edhOp :: EdhValue -> EdhValue -> EdhHostProc
        edhOp !x !y =
          evalInfix "**" (LitExpr $ ValueLiteral x) (LitExpr $ ValueLiteral y)
     in toDyn edhOp
  _ -> toDyn nil -- means not applicable here

powToOp :: Text -> Dynamic
powToOp = \case
  "float64" -> toDyn $ flip powerDouble
  "float32" -> toDyn $ flip powerFloat
  "int64" -> toDyn $ flip ((^) :: Int64 -> Int64 -> Int64)
  "int32" -> toDyn $ flip ((^) :: Int32 -> Int32 -> Int32)
  "int8" -> toDyn $ flip ((^) :: Int8 -> Int8 -> Int8)
  "byte" -> toDyn $ flip ((^) :: Word8 -> Word8 -> Word8)
  "intp" -> toDyn $ flip ((^) :: Int -> Int -> Int)
  "decimal" -> toDyn $ flip D.powerDecimal
  "box" ->
    let edhOp :: EdhValue -> EdhValue -> EdhHostProc
        edhOp !x !y =
          evalInfix "**" (LitExpr $ ValueLiteral y) (LitExpr $ ValueLiteral x)
     in toDyn edhOp
  _ -> toDyn nil -- means not applicable here

idxAssignColumn :: Column -> EdhValue -> EdhValue -> EdhHostProc
idxAssignColumn col'@(Column !col) !idxVal !other !exit !ets =
  castObjectStore' (edhUltimate other) >>= \case
    -- assign column to column
    Just (_, colOther'@(Column !colOther)) ->
      let !dtOther = data'type'of'column colOther
       in if dtOther /= dt
            then
              throwEdh ets UsageError $
                "assigning column of dtype="
                  <> data'type'identifier dtOther
                  <> " to dtype="
                  <> data'type'identifier dt
                  <> " not supported."
            else
              castObjectStore' idxVal >>= \case
                Just (_, idxCol'@(Column !idxCol)) ->
                  case data'type'identifier $ data'type'of'column idxCol of
                    "yesno" ->
                      -- yesno index
                      elemInpMaskedColumn
                        ets
                        idxCol'
                        assignOp
                        col'
                        colOther'
                        (exitEdh ets exit edhNA)
                        $ exitEdh ets exit other
                    "intp" ->
                      -- fancy index
                      elemInpFancyColumn
                        ets
                        idxCol'
                        assignOp
                        col'
                        colOther'
                        (exitEdh ets exit edhNA)
                        $ exitEdh ets exit other
                    !badDti ->
                      throwEdh ets UsageError $
                        "invalid dtype="
                          <> badDti
                          <> " for a column as an index to another column"
                Nothing -> parseEdhIndex ets idxVal $ \case
                  Left !err -> throwEdh ets UsageError err
                  Right (EdhIndex _) ->
                    throwEdh
                      ets
                      UsageError
                      "can not assign a column to a single index of another column"
                  Right EdhAny ->
                    throwEdh
                      ets
                      UsageError
                      "can not assign a column to every element of another column"
                  Right EdhAll ->
                    if dtOther /= dt
                      then
                        throwEdh ets UsageError $
                          "assigning column of dtype="
                            <> data'type'identifier dtOther
                            <> " to "
                            <> data'type'identifier dt
                            <> " not supported."
                      else do
                        !cl <- read'column'length col
                        !clOther <- read'column'length colOther
                        if clOther /= cl
                          then
                            throwEdh ets UsageError $
                              "column length mismatch: "
                                <> T.pack (show clOther)
                                <> " vs "
                                <> T.pack (show cl)
                          else
                            elemInpColumn
                              ets
                              assignOp
                              col'
                              colOther'
                              (exitEdh ets exit edhNA)
                              $ exitEdh ets exit other
                  Right (EdhSlice !start !stop !step) -> do
                    !cl <- read'column'length col
                    edhRegulateSlice ets cl (start, stop, step) $ \ !slice ->
                      elemInpSliceColumn
                        ets
                        slice
                        assignOp
                        col'
                        colOther'
                        (exitEdh ets exit edhNA)
                        $ exitEdh ets exit other

    -- assign scalar to column
    Nothing ->
      castObjectStore' idxVal >>= \case
        Just (_, idxCol'@(Column !idxCol)) ->
          case data'type'identifier $ data'type'of'column idxCol of
            "yesno" ->
              -- yesno index
              vecInpMaskedColumn
                ets
                idxCol'
                assignOp
                col'
                (edhUltimate other)
                (exitEdh ets exit edhNA)
                $ exitEdh ets exit other
            "intp" ->
              -- fancy index
              vecInpFancyColumn
                ets
                idxCol'
                assignOp
                col'
                (edhUltimate other)
                (exitEdh ets exit edhNA)
                $ exitEdh ets exit other
            !badDti ->
              throwEdh ets UsageError $
                "invalid dtype="
                  <> badDti
                  <> " for a column as an index to another column"
        Nothing -> parseEdhIndex ets idxVal $ \case
          Left !err -> throwEdh ets UsageError err
          Right (EdhIndex !i) ->
            unsafeWriteColumnCell ets col' i (edhUltimate other) $
              exitEdh ets exit
          Right EdhAny -> do
            !cl <- read'column'length col
            unsafeFillColumn ets col' (edhUltimate other) [0 .. cl - 1] $
              exitEdh ets exit other
          Right EdhAll -> do
            !cl <- read'column'length col
            unsafeFillColumn ets col' (edhUltimate other) [0 .. cl - 1] $
              exitEdh ets exit other
          Right (EdhSlice !start !stop !step) -> do
            !cl <- read'column'length col
            edhRegulateSlice ets cl (start, stop, step) $
              \(!iStart, !iStop, !iStep) ->
                vecInpSliceColumn
                  ets
                  (iStart, iStop, iStep)
                  assignOp
                  col'
                  (edhUltimate other)
                  (exitEdh ets exit edhNA)
                  $ exitEdh ets exit other
  where
    !dt = data'type'of'column col

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
  !ets =
    castObjectStore dto >>= \case
      Nothing -> throwEdh ets UsageError "invalid dtype"
      Just (_, !dt) -> case edhUltimate rngSpec of
        EdhPair
          (EdhPair (EdhDecimal !startN) (EdhDecimal !stopN))
          (EdhDecimal stepN) ->
            case D.decimalToInteger startN of
              Just !start -> case D.decimalToInteger stopN of
                Just !stop -> case D.decimalToInteger stepN of
                  Just !step ->
                    createRangeCol
                      dt
                      (fromInteger start)
                      (fromInteger stop)
                      (fromInteger step)
                  _ -> throwEdh ets UsageError "step is not an integer"
                _ -> throwEdh ets UsageError "stop is not an integer"
              _ -> throwEdh ets UsageError "start is not an integer"
        EdhPair (EdhDecimal !startN) (EdhDecimal !stopN) ->
          case D.decimalToInteger startN of
            Just !start -> case D.decimalToInteger stopN of
              Just !stop ->
                createRangeCol dt (fromInteger start) (fromInteger stop) $
                  if stop >= start then 1 else -1
              _ -> throwEdh ets UsageError "stop is not an integer"
            _ -> throwEdh ets UsageError "start is not an integer"
        EdhDecimal !stopN -> case D.decimalToInteger stopN of
          Just !stop ->
            createRangeCol dt 0 (fromInteger stop) $
              if stop >= 0 then 1 else -1
          _ -> throwEdh ets UsageError "stop is not an integer"
        !badRngSpec -> edhValueRepr ets badRngSpec $ \ !rngRepr ->
          throwEdh ets UsageError $
            "invalid range of "
              <> edhTypeNameOf badRngSpec
              <> ": "
              <> rngRepr
    where
      createRangeCol :: DataType -> Int -> Int -> Int -> STM ()
      createRangeCol !dt !start !stop !step =
        resolveNumDataType ets (data'type'identifier dt) $ \ !ndt ->
          flat'new'range'array ndt ets start stop step $ \ !cs -> do
            !csv <- newTVar cs
            !clv <- newTVar $ flatArrayCapacity cs
            let !col = Column $ InMemColumn dt csv clv
            edhCreateHostObj colClass col
              >>= exitEdh ets exit
                . EdhObject

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
