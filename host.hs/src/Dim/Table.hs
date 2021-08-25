module Dim.Table where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Monad
import Data.Dynamic
import Data.Lossless.Decimal as D
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Vector.Mutable as MV
import Dim.Column
import Dim.DataType
import Dim.InMem
import Dim.XCHG
import Language.Edh.EHI
import Prelude

{- HLINT ignore "Redundant <$>" -}

data Table = Table
  { -- | Capacity allocated for maximum number of rows
    -- i.e. minimum capacity among all columns
    table'capacity :: !(TVar Int),
    -- | Number of valid rows in this table
    -- i.e. minimum length among all columns
    table'row'count :: !(TVar Int),
    -- | Underlying table storage, represented as Column objects
    --
    -- grow/change of table capacity/count will be propagated to all these
    -- column objects, as column capacity/length
    table'columns :: !(IOPD AttrKey Object)
    -- todo add column labels
  }

withTable :: Object -> EdhTx -> (Object -> Table -> EdhTx) -> EdhTx
withTable !obj naExit !tblExit !ets = do
  supers <- readTVar $ edh'obj'supers obj
  withComposition $ obj : supers
  where
    withComposition :: [Object] -> STM ()
    withComposition [] = runEdhTx ets naExit
    withComposition (o : rest) = case fromDynamic =<< dynamicHostData o of
      Nothing -> withComposition rest
      Just (tbl :: Table) -> runEdhTx ets $ tblExit o tbl

withTblCols :: Table -> EdhTxExit [(AttrKey, Object, SomeColumn)] -> EdhTx
withTblCols (Table _cv _rcv !tcols) !exit !ets = do
  !colObjs <- iopdToList tcols
  runEdhTx ets $ seqEdhTx (extractCol <$> colObjs) exit
  where
    extractCol ::
      (AttrKey, Object) -> EdhTxExit (AttrKey, Object, SomeColumn) -> EdhTx
    extractCol (!colKey, !colObj) !exit' = withColumn' colObj naExit $
      \ !colInst !col -> exitEdhTx exit' (colKey, colInst, col)

    naExit = throwEdhTx EvalError "bug: non-Column object in Table"

readTableRow :: Table -> Int -> (KwArgs -> EdhTx) -> EdhTx
readTableRow tbl@(Table _cv !rcv _tcols) !i !exit !ets = do
  !rc <- readTVar rcv
  edhRegulateIndex ets rc i $ \ !rowIdx -> runEdhTx ets $
    withTblCols tbl $ \ !cols -> do
      let readCell ::
            (AttrKey, Object, SomeColumn) ->
            EdhTxExit (AttrKey, EdhValue) ->
            EdhTx
          readCell (colKey, _colInst, SomeColumn _ col) !cellExit =
            edhContIO $
              view'column'data col >>= \(cs, _cl) -> do
                !hv <- array'reader cs rowIdx
                atomically $ runEdhTx ets $ toEdh hv $ cellExit . (colKey,)
      seqEdhTx (readCell <$> cols) $
        exitEdhTx exit . odFromList

growTable :: ArrayCapacity -> Table -> EdhTxExit () -> EdhTx
growTable !newCap tbl@(Table cv rcv _tcols) !exit
  | newCap <= 0 =
    throwEdhTx UsageError $
      "you don't grow table capacity to " <> T.pack (show newCap)
  | otherwise = withTblCols tbl $ \ !cols !ets -> do
    !cap <- readTVar cv
    !rc <- readTVar rcv
    -- if shrinking, update table capacity before updating any column
    -- so if it's to fail halfway we are still safe
    when (newCap < cap) $ writeTVar cv newCap
    -- update row count now in case it's being shortened
    when (newCap < rc) $ writeTVar rcv newCap
    -- now shrink all columns
    runEdhTx ets $
      edhContIO $ do
        sequence_ $ grow1 <$> cols
        atomically $ do
          -- update table capacity after all columns successfully updated
          writeTVar cv newCap
          exitEdh ets exit ()
  where
    grow1 :: (AttrKey, Object, SomeColumn) -> IO ()
    grow1 (_, _, SomeColumn _ !col) = void $ grow'column'capacity col newCap

markTable :: ArrayLength -> Table -> EdhTxExit () -> EdhTx
markTable !newCnt tbl@(Table cv rcv _tcols) !exit = withTblCols tbl $
  \ !cols !ets -> do
    !cap <- readTVar cv
    if newCnt < 0 || newCnt > cap
      then
        throwEdh ets UsageError $
          "table row count out of range: " <> T.pack (show newCnt) <> " vs "
            <> T.pack (show cap)
      else do
        !rc <- readTVar rcv
        -- update row count now in case it's being shortened
        when (newCnt < rc) $ writeTVar rcv newCnt
        -- now mark all columns
        runEdhTx ets $
          edhContIO $ do
            sequence_ $ mark1 <$> cols
            atomically $ do
              -- update table row count after all columns successfully updated
              writeTVar rcv newCnt
              exitEdh ets exit ()
  where
    mark1 :: (AttrKey, Object, SomeColumn) -> IO ()
    mark1 (_, _, SomeColumn _ !col) = mark'column'length col newCnt

createTableClass :: Object -> Object -> Scope -> STM Object
createTableClass !dtBox !clsColumn !clsOuterScope =
  mkHostClass clsOuterScope "Table" (allocEdhObj tblAllocator) [] $
    \ !clsScope -> do
      !mths <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc clsScope vc nm hp
            | (nm, vc, hp) <-
                [ ("__cap__", EdhMethod, wrapHostProc tblCapProc),
                  ("__len__", EdhMethod, wrapHostProc tblLenProc),
                  ("__grow__", EdhMethod, wrapHostProc tblGrowProc),
                  ("__mark__", EdhMethod, wrapHostProc tblMarkRowCntProc),
                  ("(@)", EdhMethod, wrapHostProc tblAttrReadProc),
                  ("(@=)", EdhMethod, wrapHostProc tblAttrWriteProc),
                  ("([])", EdhMethod, wrapHostProc tblIdxReadProc),
                  ("([=])", EdhMethod, wrapHostProc tblIdxWriteProc),
                  ("__repr__", EdhMethod, wrapHostProc tblReprProc),
                  ("__show__", EdhMethod, wrapHostProc tblShowProc),
                  ("__desc__", EdhMethod, wrapHostProc tblDescProc)
                ]
          ]
            ++ [ (AttrByName nm,) <$> mkHostProperty clsScope nm getter setter
                 | (nm, getter, setter) <-
                     [ ("columns", tblColsGetterProc, Nothing)
                     ]
               ]
      iopdUpdate mths $ edh'scope'entity clsScope
  where
    tblAllocator ::
      "capacity" !: Int ->
      "row'count" ?: Int ->
      "columns" !: KeywordArgs ->
      ArgsPack -> -- allow/ignore arbitrary ctor args for descendant classes
      EdhObjectAllocator
    tblAllocator
      (mandatoryArg -> !ctorCap)
      (defaultArg ctorCap -> !ctorCnt)
      (mandatoryArg -> KeywordArgs !colSpecs)
      _ctorOtherArgs
      !ctorExit
      !etsCtor
        | ctorCap <= 0 =
          throwEdh etsCtor UsageError $
            "table capacity should be a positive integer, not "
              <> T.pack (show ctorCap)
        | ctorCnt < 0 =
          throwEdh etsCtor UsageError $
            "table row count should be zero or a positive integer, not "
              <> T.pack (show ctorCnt)
        | otherwise = runEdhTx etsCtor $
          seqEdhTx (adaptColSpec <$> odToList colSpecs) $ \ !ces _ets -> do
            !cv <- newTVar ctorCap
            !rcv <- newTVar ctorCnt
            !tcols <- iopdFromList ces
            ctorExit Nothing $ HostStore $ toDyn $ Table cv rcv tcols
        where
          adaptColSpec ::
            (AttrKey, EdhValue) -> EdhTxExit (AttrKey, Object) -> EdhTx
          adaptColSpec (colKey, colSpec) !exit = case edhUltimate colSpec of
            EdhObject !obj -> do
              let tryDt = withDataType obj trySeq $ \ !dt ->
                    createInMemColumn dt ctorCap ctorCnt $ \ !col !ets ->
                      edhCreateHostObj' clsColumn (toDyn col) [obj]
                        >>= exitEdh ets exit . (colKey,)

                  trySeq = case fromDynamic =<< dynamicHostData obj of
                    Nothing -> badSpec
                    Just (vec :: MV.IOVector EdhValue) ->
                      if MV.length vec < ctorCnt
                        then
                          throwEdhTx UsageError $
                            "Sequence " <> attrKeyStr colKey
                              <> " is not long enough: "
                              <> T.pack (show $ MV.length vec)
                              <> " vs "
                              <> T.pack (show ctorCnt)
                        else \ !ets -> do
                          -- todo should we copy the mutable IO vector?
                          !csv <- newTMVar $ DirectArray vec
                          !clv <- newTVar ctorCnt
                          !colObj <-
                            edhCreateHostObj'
                              clsColumn
                              (toDyn $ someColumn $ InMemDirCol csv clv)
                              [dtBox]
                          exitEdh ets exit (colKey, colObj)

              withColumn' obj tryDt $ \_colInst (SomeColumn _ !col) ->
                edhContIO $
                  view'column'data col >>= \(!cs, !cl) ->
                    if array'capacity cs < ctorCap || cl < ctorCnt
                      then
                        atomically $
                          throwEdh etsCtor UsageError $
                            "Column "
                              <> attrKeyStr colKey
                              <> " is not long enough: "
                              <> T.pack (show cl)
                              <> "/"
                              <> T.pack (show $ array'capacity cs)
                              <> " vs "
                              <> T.pack (show ctorCnt)
                              <> "/"
                              <> T.pack (show ctorCap)
                      else do
                        -- todo leave a longer column w/o truncating it?
                        mark'column'length col ctorCnt
                        atomically $ exitEdh etsCtor exit (colKey, obj)
            EdhArgsPack (ArgsPack !args !kwargs)
              | odNull kwargs -> createBoxCol args $ exit . (colKey,)
            EdhList (List _ !lv) -> \ !ets -> do
              !vs <- readTVar lv
              runEdhTx ets $ createBoxCol vs $ exit . (colKey,)
            -- TODO support range, slice, etc. w/ optional dtype
            _ -> badSpec
            where
              badSpec = edhSimpleDescTx colSpec $ \ !badDesc ->
                throwEdhTx UsageError $
                  "invalid column specification for "
                    <> attrKeyStr colKey
                    <> " - "
                    <> badDesc

          createBoxCol :: [EdhValue] -> EdhTxExit Object -> EdhTx
          createBoxCol !es !exit !ets = runEdhTx ets $
            edhContIO $ do
              !iov <- MV.unsafeNew ctorCap
              let fillElems :: Int -> [EdhValue] -> IO Int
                  fillElems i [] = return i
                  fillElems i (e : rest)
                    | i >= ctorCap = return i
                    | otherwise = do
                      MV.unsafeWrite iov i e
                      fillElems (i + 1) rest
                  fillNA :: Int -> IO ()
                  fillNA i
                    | i >= ctorCap = return ()
                    | otherwise = do
                      MV.unsafeWrite iov i edhNA
                      fillNA $ i + 1
              fillElems 0 es >>= fillNA
              atomically $ do
                !csv <- newTMVar $ DirectArray iov
                !clv <- newTVar ctorCnt
                !colObj <-
                  edhCreateHostObj'
                    clsColumn
                    (toDyn $ someColumn $ InMemDirCol csv clv)
                    [dtBox]
                exitEdh ets exit colObj

    withThisTable :: (Object -> Table -> EdhTx) -> EdhTx
    withThisTable !tblExit !ets =
      case dynamicHostData this of
        Nothing ->
          throwEdh ets EvalError "bug: not even a host value for Table"
        Just !dd -> case fromDynamic dd of
          Nothing ->
            throwEdh ets EvalError $
              "bug: this is not a Table but " <> T.pack (show dd)
          Just !tbl -> exitEdh ets (tblExit this) tbl
      where
        this = edh'scope'this $ contextScope $ edh'context ets

    tblColsGetterProc :: EdhHostProc
    tblColsGetterProc !exit = withThisTable $ \_this (Table _ _ !tcols) !ets ->
      odTransform EdhObject <$> iopdSnapshot tcols
        >>= exitEdh ets exit . EdhArgsPack . ArgsPack []

    tblCapProc :: EdhHostProc
    tblCapProc !exit = withThisTable $ \_this (Table !cv _rcv _tcols) !ets -> do
      !cap <- readTVar cv
      exitEdh ets exit $ EdhDecimal $ fromIntegral cap

    tblLenProc :: EdhHostProc
    tblLenProc !exit = withThisTable $ \_this (Table _cv !rcv _tcols) !ets -> do
      !rc <- readTVar rcv
      exitEdh ets exit $ EdhDecimal $ fromIntegral rc

    tblGrowProc :: "newCap" !: Int -> EdhHostProc
    tblGrowProc (mandatoryArg -> !newCap) !exit = withThisTable $
      \_this !tbl -> growTable newCap tbl $ exit . const nil

    tblMarkRowCntProc :: "newCnt" !: Int -> EdhHostProc
    tblMarkRowCntProc (mandatoryArg -> !newCnt) !exit = withThisTable $
      \_this !tbl -> markTable newCnt tbl $ exit . const nil

    tblAttrReadProc :: EdhValue -> EdhHostProc
    tblAttrReadProc !keyVal !exit = withThisTable $
      \_this (Table _ _ !tcols) !ets ->
        edhValueAsAttrKey ets keyVal $ \ !attrKey ->
          iopdLookup attrKey tcols >>= \case
            Nothing -> exitEdh ets exit edhNA
            Just !tcol -> exitEdh ets exit $ EdhObject tcol

    tblAttrWriteProc :: EdhValue -> "toVal" ?: EdhValue -> EdhHostProc
    tblAttrWriteProc !attrKey (optionalArg -> !maybeAttrVal) !exit =
      withThisTable $ \_this (Table !cv !rcv !tcols) !ets ->
        edhValueAsAttrKey ets attrKey $ \ !colKey -> case maybeAttrVal of
          Nothing -> do
            iopdDelete colKey tcols
            exitEdh ets exit nil
          Just !attrVal -> do
            !cap <- readTVar cv
            !rc <- readTVar rcv
            let badColSrc = edhSimpleDescTx attrVal $ \ !badDesc ->
                  throwEdhTx UsageError $
                    "not assignable to a table column: " <> badDesc
            runEdhTx ets $ case edhUltimate attrVal of
              EdhObject !obj -> do
                let tryDt = withDataType obj trySeq $ \ !dt ->
                      createInMemColumn dt cap rc $ \ !col _ets -> do
                        !colObj <- edhCreateHostObj' clsColumn (toDyn col) [obj]
                        iopdInsert colKey colObj tcols
                        exitEdh ets exit $ EdhObject colObj

                    trySeq = case fromDynamic =<< dynamicHostData obj of
                      Nothing -> badColSrc
                      Just (vec :: MV.IOVector EdhValue) ->
                        if MV.length vec < rc
                          then
                            throwEdhTx UsageError $
                              "Sequence " <> attrKeyStr colKey
                                <> " is not long enough: "
                                <> T.pack (show $ MV.length vec)
                                <> " vs "
                                <> T.pack (show rc)
                          else \_ets -> do
                            -- todo should we copy the mutable IO vector?
                            !csv <- newTMVar $ DirectArray vec
                            !clv <- newTVar rc
                            !colObj <-
                              edhCreateHostObj'
                                clsColumn
                                (toDyn $ someColumn $ InMemDirCol csv clv)
                                [dtBox]
                            iopdInsert colKey colObj tcols
                            exitEdh ets exit $ EdhObject colObj

                withColumn' obj tryDt $ \_colInst (SomeColumn _ !col) ->
                  edhContIO $
                    view'column'data col >>= \(!cs, !cl) ->
                      if array'capacity cs < cap || cl < rc
                        then
                          atomically $
                            throwEdh ets UsageError $
                              "Column "
                                <> attrKeyStr colKey
                                <> " is not long enough: "
                                <> T.pack (show cl)
                                <> "/"
                                <> T.pack (show $ array'capacity cs)
                                <> " vs "
                                <> T.pack (show rc)
                                <> "/"
                                <> T.pack (show cap)
                        else do
                          -- todo leave a longer column w/o truncating it?
                          mark'column'length col rc
                          atomically $ do
                            iopdInsert colKey obj tcols
                            exitEdh ets exit $ EdhObject obj
              _ -> badColSrc

    tblIdxReadProc :: EdhValue -> EdhHostProc
    tblIdxReadProc !idxVal !tblExit !ets = runEdhTx ets $
      withThisTable $
        \ !thisTbl !tbl -> withTblCols tbl $ \ !tcols -> do
          -- let that = edh'scope'that $ contextScope $ edh'context ets
          let withBoolIdx ::
                forall c f.
                ManagedColumn c f YesNo =>
                Object ->
                c YesNo ->
                EdhTx
              withBoolIdx _ !idxCol = idxCols $ \ !thisCol !col !colExit ->
                extractColumnBool thisCol col idxCol $
                  \(!newColObj, SomeColumn _ !newCol) ->
                    edhContIO $
                      view'column'data newCol >>= \(!cs, !cl) ->
                        atomically $
                          exitEdh ets colExit (newColObj, array'capacity cs, cl)

              withIntpIdx ::
                forall c f.
                ManagedColumn c f Int =>
                Object ->
                c Int ->
                EdhTx
              withIntpIdx _ !idxCol = idxCols $ \ !thisCol !col !colExit ->
                extractColumnFancy thisCol col idxCol $
                  \(!newColObj, SomeColumn _ !newCol) ->
                    edhContIO $
                      view'column'data newCol >>= \(!cs, !cl) ->
                        atomically $
                          exitEdh ets colExit (newColObj, array'capacity cs, cl)

              withEdhIdx :: EdhTx
              withEdhIdx _ets = parseEdhIndex ets idxVal $ \case
                Left !err -> throwEdh ets UsageError err
                Right !idx -> case idx of
                  EdhIndex !i ->
                    runEdhTx ets $
                      readTableRow tbl i $
                        exitEdhTx tblExit . (EdhArgsPack . ArgsPack [])
                  EdhAny -> exitEdh ets tblExit $ EdhObject that
                  EdhAll -> exitEdh ets tblExit $ EdhObject that
                  EdhSlice !start !stop !step -> do
                    !rowCnt <- readTVar (table'row'count tbl)
                    edhRegulateSlice ets rowCnt (start, stop, step) $
                      \(!iStart, !iStop, !iStep) -> runEdhTx ets $
                        idxCols $ \ !thisCol !col !colExit ->
                          sliceColumn thisCol col iStart iStop iStep $
                            \(!newColObj, SomeColumn _ !newCol) ->
                              edhContIO $
                                view'column'data newCol >>= \(!cs, !cl) ->
                                  atomically $
                                    exitEdh
                                      ets
                                      colExit
                                      (newColObj, array'capacity cs, cl)
                where
                  that = edh'scope'that $ contextScope $ edh'context ets

              idxCols ::
                ( Object ->
                  SomeColumn ->
                  EdhTxExit (Object, ArrayCapacity, ArrayLength) ->
                  EdhTx
                ) ->
                EdhTx
              idxCols doCol _ets = do
                !rowCap <- readTVar $ table'capacity tbl
                !rowCnt <- readTVar $ table'row'count tbl
                let go ::
                      ArrayCapacity ->
                      ArrayLength ->
                      [(AttrKey, Object)] ->
                      [(AttrKey, Object, SomeColumn)] ->
                      STM ()
                    go !rowCap' !rowCnt' rCols [] = do
                      !cv' <- newTVar rowCap'
                      !rcv' <- newTVar rowCnt'
                      !tcols' <- iopdFromList $ reverse rCols
                      edhCloneHostObj
                        ets
                        thisTbl
                        (edh'scope'that $ contextScope $ edh'context ets)
                        (Table cv' rcv' tcols')
                        (exitEdh ets tblExit . EdhObject)
                    go
                      !rowCap'
                      !rowCnt'
                      rCols
                      ((!colKey, !colObj, !col) : rest) = runEdhTx ets $
                        doCol colObj col $
                          \(!colObj', cap', cl') _ets ->
                            go
                              (min cap' rowCap')
                              (min cl' rowCnt')
                              ((colKey, colObj') : rCols)
                              rest
                go rowCap rowCnt [] tcols

          withColumnOf' @YesNo
            idxVal
            (withColumnOf' @Int idxVal withEdhIdx withIntpIdx)
            withBoolIdx

    tblIdxWriteProc :: EdhValue -> EdhValue -> EdhHostProc
    tblIdxWriteProc !idxVal !toVal !exit = withThisTable $
      \_this !tbl -> withTblCols tbl $ \ !tcols !ets -> do
        let assignCols :: EdhTxExit [(SomeColumn, EdhValue)]
            assignCols [] = exitEdhTx exit toVal
            assignCols ((!col, !tgtVal) : rest) =
              idxAssignColumn col idxVal tgtVal $ assignCols rest

            matchColTgts ::
              [(AttrKey, Object, SomeColumn)] ->
              EdhTx
            matchColTgts !cols = case edhUltimate toVal of
              -- assign with an apk
              EdhArgsPack (ArgsPack !tgts !kwtgts) ->
                matchApk [] cols tgts kwtgts
              EdhObject !obj ->
                withTable obj broadcastMatch $
                  \_ (Table _ _ !tcolsOther) _ets -> do
                    -- todo validate shape match here?
                    !colsOther <- iopdSnapshot tcolsOther
                    runEdhTx ets $ matchTbl [] cols colsOther
              _ -> broadcastMatch
              where
                broadcastMatch :: EdhTx
                broadcastMatch =
                  assignCols $ (\(_, _, !col) -> (col, toVal)) <$> cols

                matchApk ::
                  [(SomeColumn, EdhValue)] ->
                  [(AttrKey, Object, SomeColumn)] ->
                  [EdhValue] ->
                  KwArgs ->
                  EdhTx
                matchApk ms [] _ _ = assignCols $! reverse ms
                matchApk ms ((!colKey, _colInst, !col) : rest) !tgts !kwtgts =
                  case odLookup colKey kwtgts of
                    Just !tgtVal ->
                      matchApk ((col, tgtVal) : ms) rest tgts kwtgts
                    Nothing -> case tgts of
                      [] -> matchApk ms rest [] kwtgts
                      tgtVal : tgts' ->
                        matchApk ((col, tgtVal) : ms) rest tgts' kwtgts

                matchTbl ::
                  [(SomeColumn, EdhValue)] ->
                  [(AttrKey, Object, SomeColumn)] ->
                  OrderedDict AttrKey Object ->
                  EdhTx
                matchTbl ms [] _ = assignCols $! reverse ms
                matchTbl ms ((!colKey, _colInst, !col) : rest) !colsOther =
                  case odLookup colKey colsOther of
                    Nothing -> matchTbl ms rest colsOther
                    Just !colOther ->
                      matchTbl
                        ((col, EdhObject colOther) : ms)
                        rest
                        colsOther
        runEdhTx ets $ matchColTgts tcols

    tblReprProc :: EdhHostProc
    tblReprProc !exit = withThisTable $
      \_this (Table !cv !rcv !tcols) !ets -> do
        !cap <- readTVar cv
        !rc <- readTVar rcv
        !tcl <- iopdToList tcols
        let badColDt = throwEdh ets EvalError "bug: Table Column missing dtype"
            colShortRepr :: (AttrKey, Object) -> EdhTxExit Text -> EdhTx
            colShortRepr (!colKey, !colObj) !exit' _ets =
              getColumnDtype' colObj badColDt $ \ !dto ->
                withDataType dto badColDt $ \ !dt ->
                  exitEdh ets exit' $
                    attrKeyStr colKey <> "= " <> data'type'ident dt <> ", "
        runEdhTx ets $
          seqEdhTx (colShortRepr <$> tcl) $ \ !colReprs ->
            exitEdhTx exit $
              EdhString $
                "Table( "
                  <> T.pack (show cap)
                  <> ", "
                  <> T.pack (show rc)
                  <> ", "
                  <> T.concat colReprs
                  <> ")"

    tblShowProc :: "columnWidth" ?: PackedArgs -> EdhHostProc
    tblShowProc
      ( defaultArg (PackedArgs (ArgsPack [] odEmpty)) ->
          PackedArgs (ArgsPack !posWidth !kwWidth)
        )
      !exit = withThisTable $ \_this tbl@(Table _cv !rcv !tcols) !ets -> do
        !rowCnt <- readTVar rcv
        !colCnt <- iopdSize tcols
        !posColWidth <- newTVar posWidth
        let specifiedColWidth :: AttrKey -> (Int -> STM ()) -> STM ()
            specifiedColWidth !colKey !cwExit = case odLookup colKey kwWidth of
              Just !cwv -> parseColWidth cwv
              Nothing ->
                readTVar posColWidth >>= \case
                  [] -> cwExit 10
                  [cwv] -> parseColWidth cwv
                  (cwv : rest) -> do
                    writeTVar posColWidth rest
                    parseColWidth cwv
              where
                parseColWidth :: EdhValue -> STM ()
                parseColWidth !cwVal = case edhUltimate cwVal of
                  EdhDecimal !d -> case D.decimalToInteger d of
                    Just !i | i > 0 && i < 2000 -> cwExit $ fromInteger i
                    _ -> edhValueDesc ets cwVal $ \ !cwDesc ->
                      throwEdh ets UsageError $
                        "invalid columnWidth: " <> cwDesc
                  _ -> edhValueDesc ets cwVal $ \ !cwDesc ->
                    throwEdh ets UsageError $
                      "invalid columnWidth: " <> cwDesc

            prepareCols ::
              EdhTxExit [(Text, Int, Int -> (Text -> IO ()) -> IO ())] ->
              [(AttrKey, Object, SomeColumn)] ->
              EdhTx
            prepareCols !colsExit !cols _ets =
              prepareSpecs [] cols
              where
                prepareSpecs ::
                  [(Text, Int, Int -> (Text -> IO ()) -> IO ())] ->
                  [(AttrKey, Object, SomeColumn)] ->
                  STM ()
                prepareSpecs specs [] =
                  runEdhTx ets $ colsExit $! reverse specs
                prepareSpecs
                  specs
                  ((!colKey, _colObj, SomeColumn _ !col) : rest) =
                    specifiedColWidth colKey $ \ !colWidth ->
                      runEdhTx ets $
                        edhContIO $
                          view'column'data col >>= \(!cs, _cl) ->
                            atomically $ do
                              let readCell !rowIdx !cellExit = do
                                    !hvCell <- array'reader cs rowIdx
                                    atomically $
                                      runEdhTx ets $
                                        toEdh hvCell $
                                          \ !vCell -> edhValueStrTx vCell $
                                            \ !reprCell ->
                                              edhContIO $ cellExit reprCell

                              prepareSpecs
                                ( (attrKeyStr colKey, colWidth, readCell) :
                                  specs
                                )
                                rest

        runEdhTx ets $
          withTblCols tbl $
            prepareCols $ \ !colSpecs -> do
              let !titleLine =
                    T.concat $
                      (<$> colSpecs) $ \(!title, !colWidth, _readCell) ->
                        centerBriefAlign (colWidth + 1) title
                  !totalWidth = T.length titleLine
              let rowLine :: Int -> (Text -> IO ()) -> IO ()
                  rowLine !i !rowLineExit = readCells "|" colSpecs
                    where
                      readCells !line [] = rowLineExit line
                      readCells !line ((_title, !colWidth, !readCell) : rest) =
                        readCell i $ \ !cellStr ->
                          readCells
                            ( line
                                <> centerBriefAlign (colWidth + 1) cellStr
                            )
                            rest
                  rowLines :: [Int] -> ([Text] -> IO ()) -> IO ()
                  rowLines !rowIdxs !rowLinesExit = go [] rowIdxs
                    where
                      go !rls [] = rowLinesExit $ reverse rls
                      go !rls (rowIdx : rest) =
                        rowLine rowIdx $ \ !line -> go (line : rls) rest
                  dataLines :: ([Text] -> IO ()) -> IO ()
                  dataLines !dataLinesExit =
                    if rowCnt <= 20
                      then -- TODO make this tunable
                        rowLines [0 .. rowCnt - 1] dataLinesExit
                      else rowLines [0 .. 10] $ \ !headLines ->
                        rowLines [rowCnt - 11 .. rowCnt - 1] $ \ !tailLines ->
                          dataLinesExit $ headLines <> ["..."] <> tailLines
              edhContIO $
                dataLines $ \ !dls ->
                  atomically $
                    exitEdh ets exit $
                      EdhString $
                        T.replicate (totalWidth + 1) "-"
                          <> "\n|"
                          <> centerBriefAlign
                            totalWidth
                            ( "Table "
                                <> T.pack (show colCnt)
                                <> " × "
                                <> T.pack (show rowCnt)
                            )
                          <> "\n|"
                          <> T.replicate (totalWidth - 1) "-"
                          <> "|\n|"
                          <> titleLine
                          <> "\n|"
                          <> T.replicate (totalWidth - 1) "-"
                          <> "|\n"
                          <> T.unlines dls
                          <> T.replicate (totalWidth + 1) "-"

    tblDescProc :: RestKwArgs -> EdhHostProc
    tblDescProc !kwargs !exit = withThisTable $
      \_this (Table _cv !rcv !tcols) !ets -> do
        !rowCnt <- readTVar rcv
        !colCnt <- iopdSize tcols
        !cols <- iopdToList tcols
        let tcDesc :: (AttrKey, Object) -> EdhTxExit Text -> EdhTx
            tcDesc (!colKey, !colObj) !exit' =
              edhObjDescTx' colObj kwargs $ \ !colDesc ->
                exitEdhTx exit' $
                  " ** Table Column: "
                    <> T.pack (show colKey)
                    <> " :\n"
                    <> colDesc
        runEdhTx ets $
          seqEdhTx (tcDesc <$> cols) $ \ !tcDescLines ->
            exitEdhTx exit $
              EdhString $
                " * Table of " <> T.pack (show colCnt) <> " column(s) × "
                  <> T.pack (show rowCnt)
                  <> " row(s) \n"
                  <> T.unlines tcDescLines

centerBriefAlign :: Int -> Text -> Text
centerBriefAlign !dispWidth !txt
  | dispWidth < 4 =
    let !txt' = T.take dispWidth txt
        !len = T.length txt'
     in if len < dispWidth
          then txt' <> T.replicate (dispWidth - len) " "
          else txt'
centerBriefAlign !dispWidth !txt =
  if len < dispWidth
    then
      let (!margin, !rightPadding) = quotRem (dispWidth - len) 2
       in T.replicate margin " "
            <> txt
            <> T.replicate (margin - 1 + rightPadding) " "
            <> "|"
    else T.take (dispWidth - 4) txt <> "...|"
  where
    !len = T.length txt
