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

withTblCols :: Table -> EdhTxExit [(Object, SomeColumn)] -> EdhTx
withTblCols (Table _cv _rcv !tcols) !exit !ets = do
  !colObjs <- iopdValues tcols
  runEdhTx ets $ seqEdhTx (extractCol <$> colObjs) exit
  where
    extractCol :: Object -> EdhTxExit (Object, SomeColumn) -> EdhTx
    extractCol co !exit' = withColumn' co naExit $ curry $ exitEdhTx exit'
    naExit = throwEdhTx EvalError "bug: non-Column object in Table"

readTableRow :: Table -> Int -> (KwArgs -> EdhTx) -> EdhTx
readTableRow tbl@(Table _cv !rcv !tcols) !i !exit !ets = do
  !rc <- readTVar rcv
  !ks <- iopdKeys tcols
  edhRegulateIndex ets rc i $ \ !rowIdx -> runEdhTx ets $
    withTblCols tbl $ \ !cols -> do
      let readCell :: SomeColumn -> EdhTxExit EdhValue -> EdhTx
          readCell (SomeColumn _ col) !cellExit = view'column'data col $
            \(cs, _cl) -> edhContIO $ do
              !hv <- array'reader cs rowIdx
              atomically $ runEdhTx ets $ toEdh hv cellExit
      seqEdhTx (readCell . snd <$> cols) $ \ !vs ->
        exitEdhTx exit $ odFromList $ zip ks vs

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
      seqEdhTx (grow1 . snd <$> cols) $ \_ _ets -> do
        -- update table capacity after all columns successfully updated
        writeTVar cv newCap
        exitEdh ets exit ()
  where
    grow1 :: SomeColumn -> EdhTxExit () -> EdhTx
    grow1 (SomeColumn _ !col) = grow'column'capacity col newCap

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
          seqEdhTx (mark1 . snd <$> cols) $ \_ _ets -> do
            -- update table row count after all columns successfully updated
            writeTVar rcv newCnt
            exitEdh ets exit ()
  where
    mark1 :: SomeColumn -> EdhTxExit () -> EdhTx
    mark1 (SomeColumn _ !col) = mark'column'length col newCnt

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
                view'column'data col $ \(!cs, !cl) ->
                  if array'capacity cs < ctorCap || cl < ctorCnt
                    then
                      throwEdhTx UsageError $
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
                    else -- todo leave a longer column w/o truncating it?
                    mark'column'length col ctorCnt $ \() ->
                      exitEdhTx exit (colKey, obj)
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

    withThisTable :: (Table -> EdhTx) -> EdhTx
    withThisTable !tblExit !ets = case fromDynamic =<< dynamicHostData this of
      Nothing -> throwEdh ets UsageError "bug: this is not a Table"
      Just !tbl -> exitEdh ets tblExit tbl
      where
        this = edh'scope'this $ contextScope $ edh'context ets

    tblColsGetterProc :: EdhHostProc
    tblColsGetterProc !exit = withThisTable $ \(Table _ _ !tcols) !ets ->
      odTransform EdhObject <$> iopdSnapshot tcols
        >>= exitEdh ets exit . EdhArgsPack . ArgsPack []

    tblCapProc :: EdhHostProc
    tblCapProc !exit = withThisTable $ \(Table !cv _rcv _tcols) !ets -> do
      !cap <- readTVar cv
      exitEdh ets exit $ EdhDecimal $ fromIntegral cap

    tblLenProc :: EdhHostProc
    tblLenProc !exit = withThisTable $ \(Table _cv !rcv _tcols) !ets -> do
      !rc <- readTVar rcv
      exitEdh ets exit $ EdhDecimal $ fromIntegral rc

    tblGrowProc :: "newCap" !: Int -> EdhHostProc
    tblGrowProc (mandatoryArg -> !newCap) !exit = withThisTable $
      \ !tbl -> growTable newCap tbl $ exit . const nil

    tblMarkRowCntProc :: "newCnt" !: Int -> EdhHostProc
    tblMarkRowCntProc (mandatoryArg -> !newCnt) !exit = withThisTable $
      \ !tbl -> markTable newCnt tbl $ exit . const nil

    tblAttrReadProc :: EdhValue -> EdhHostProc
    tblAttrReadProc !keyVal !exit = withThisTable $ \(Table _ _ !tcols) !ets ->
      edhValueAsAttrKey ets keyVal $ \ !attrKey ->
        iopdLookup attrKey tcols >>= \case
          Nothing -> exitEdh ets exit edhNA
          Just !tcol -> exitEdh ets exit $ EdhObject tcol

    tblAttrWriteProc :: EdhValue -> "toVal" ?: EdhValue -> EdhHostProc
    tblAttrWriteProc !attrKey (optionalArg -> !maybeAttrVal) !exit =
      withThisTable $ \(Table !cv !rcv !tcols) !ets ->
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
                  view'column'data col $ \(!cs, !cl) ->
                    if array'capacity cs < cap || cl < rc
                      then
                        throwEdhTx UsageError $
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
                      else -- todo leave a longer column w/o truncating it?
                      mark'column'length col rc $ \() _ets -> do
                        iopdInsert colKey obj tcols
                        exitEdh ets exit $ EdhObject obj
              _ -> badColSrc

    tblIdxReadProc :: EdhValue -> EdhHostProc
    tblIdxReadProc !idxVal !exit !ets =
      undefined
    -- withThisHostObj ets $ \tbl@(Table _trCapV !trCntV !tcols) ->
    --   castObjectStore' idxVal >>= \case
    --     Just (_, idxCol'@(Column !idxCol)) ->
    --       case data'type'identifier $ data'type'of'column idxCol of
    --         "yesno" -> do
    --           -- yesno index
    --           !rtrCapV <- newTVar =<< read'column'length idxCol
    --           !rtrCntV <- newTVar 0
    --           !tcolsNew <- iopdEmpty
    --           let extractCols [] =
    --                 edhCloneHostObj
    --                   ets
    --                   thisTab
    --                   thatTab
    --                   (Table rtrCapV rtrCntV tcolsNew)
    --                   $ \ !newTabObj -> exitEdh ets exit $ EdhObject newTabObj
    --               extractCols ((!key, !thatCol) : rest) =
    --                 extractColumnBool ets thatCol idxCol' (extractCols rest) $
    --                   \ !clNew !newColObj -> do
    --                     writeTVar rtrCntV clNew
    --                     iopdInsert key newColObj tcolsNew
    --                     extractCols rest
    --           iopdToList tcols >>= extractCols
    --         "intp" -> do
    --           -- fancy index
    --           !rtrCapV <- newTVar =<< read'column'length idxCol
    --           !rtrCntV <- newTVar =<< read'column'length idxCol
    --           !tcolsNew <- iopdEmpty
    --           let extractCols [] =
    --                 edhCloneHostObj
    --                   ets
    --                   thisTab
    --                   thatTab
    --                   (Table rtrCapV rtrCntV tcolsNew)
    --                   $ \ !newTabObj -> exitEdh ets exit $ EdhObject newTabObj
    --               extractCols ((!key, !thatCol) : rest) =
    --                 extractColumnFancy
    --                   ets
    --                   thatCol
    --                   idxCol'
    --                   (extractCols rest)
    --                   $ \ !newColObj -> do
    --                     iopdInsert key newColObj tcolsNew
    --                     extractCols rest
    --           iopdToList tcols >>= extractCols
    --         !badDti ->
    --           throwEdh ets UsageError $
    --             "invalid dtype="
    --               <> badDti
    --               <> " for a column as an index to a table"
    --     Nothing -> parseEdhIndex ets idxVal $ \case
    --       Left !err -> throwEdh ets UsageError err
    --       Right (EdhIndex !i) ->
    --         readTableRow ets tbl i $ exitEdh ets exit . EdhArgsPack
    --       Right EdhAny -> exitEdh ets exit $ EdhObject thatTab
    --       Right EdhAll -> exitEdh ets exit $ EdhObject thatTab
    --       Right (EdhSlice !start !stop !step) -> do
    --         !trCnt <- readTVar trCntV
    --         edhRegulateSlice ets trCnt (start, stop, step) $
    --           \(!iStart, !iStop, !iStep) -> do
    --             !rtrCapV <- newTVar 0
    --             !rtrCntV <- newTVar 0
    --             !tcolsNew <- iopdEmpty
    --             let sliceCols [] =
    --                   edhCloneHostObj
    --                     ets
    --                     thisTab
    --                     thatTab
    --                     (Table rtrCapV rtrCntV tcolsNew)
    --                     $ \ !newTabObj ->
    --                       exitEdh ets exit $
    --                         EdhObject newTabObj
    --                 sliceCols ((!key, !thatCol) : rest) =
    --                   sliceColumn ets thatCol iStart iStop iStep $
    --                     \ !ccNew !clNew !newColObj -> do
    --                       writeTVar rtrCapV ccNew
    --                       writeTVar rtrCntV clNew
    --                       iopdInsert key newColObj tcolsNew
    --                       sliceCols rest
    --             iopdToList tcols >>= sliceCols
    -- where
    --   !thisTab = edh'scope'this $ contextScope $ edh'context ets
    --   !thatTab = edh'scope'that $ contextScope $ edh'context ets

    tblIdxWriteProc :: EdhValue -> EdhValue -> EdhHostProc
    tblIdxWriteProc !idxVal !toVal !exit !ets =
      withThisHostObj ets $ \(Table _trCapV !trCntV !tcols) ->
        readTVar trCntV
          >>= \ !trCnt -> iopdToList tcols >>= matchColTgts trCnt assignCols
      where
        assignCols :: [(Object, EdhValue)] -> STM ()
        assignCols [] = exitEdh ets exit toVal
        assignCols ((!colObj, !tgtVal) : rest) =
          undefined
        -- castTableColumn colObj >>= \ !col ->
        --   runEdhTx ets $
        --     idxAssignColumn col idxVal tgtVal $ \_ _ets ->
        --       assignCols rest

        matchColTgts ::
          Int ->
          ([(Object, EdhValue)] -> STM ()) ->
          [(AttrKey, Object)] ->
          STM ()
        matchColTgts !trc !mcExit !cols = case edhUltimate toVal of
          -- assign with an apk
          EdhArgsPack (ArgsPack !tgts !kwtgts) -> matchApk [] cols tgts kwtgts
          !toVal' ->
            castObjectStore' toVal' >>= \case
              -- assign with another table
              Just (_tblOther, Table _trCapV !trCntVOther !tcolsOther) -> do
                !trcOther <- readTVar trCntVOther
                if trc /= trcOther
                  then
                    throwEdh ets UsageError $
                      "table row count mismatch: "
                        <> T.pack (show trc)
                        <> " vs "
                        <> T.pack (show trcOther)
                  else iopdSnapshot tcolsOther >>= matchTab [] cols
              -- assign with a scalar
              Nothing -> mcExit $ (,toVal) . snd <$> cols
          where
            matchApk ::
              [(Object, EdhValue)] ->
              [(AttrKey, Object)] ->
              [EdhValue] ->
              KwArgs ->
              STM ()
            matchApk !ms [] _ _ = mcExit $! reverse ms
            matchApk !ms ((!colKey, !colObj) : rest) !tgts !kwtgts =
              case odLookup colKey kwtgts of
                Just !tgtVal ->
                  matchApk ((colObj, tgtVal) : ms) rest tgts kwtgts
                Nothing -> case tgts of
                  [] -> matchApk ms rest [] kwtgts
                  tgtVal : tgts' ->
                    matchApk ((colObj, tgtVal) : ms) rest tgts' kwtgts

            matchTab ::
              [(Object, EdhValue)] ->
              [(AttrKey, Object)] ->
              OrderedDict AttrKey Object ->
              STM ()
            matchTab !ms [] _ = mcExit $! reverse ms
            matchTab !ms ((!colKey, !colObj) : rest) !colsOther =
              case odLookup colKey colsOther of
                Nothing -> matchTab ms rest colsOther
                Just !colOther ->
                  matchTab ((colObj, EdhObject colOther) : ms) rest colsOther

    tblReprProc :: EdhHostProc
    tblReprProc !exit = withThisTable $ \(Table !cv !rcv !tcols) !ets -> do
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
      !exit = withThisTable $ \tbl@(Table _cv !rcv !tcols) !ets -> do
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
              [AttrKey] ->
              EdhTxExit [(Text, Int, Int -> (Text -> IO ()) -> IO ())] ->
              [(Object, SomeColumn)] ->
              EdhTx
            prepareCols !colKeys !colsExit !cols _ets =
              prepareSpecs [] $ zip colKeys cols
              where
                prepareSpecs ::
                  [(Text, Int, Int -> (Text -> IO ()) -> IO ())] ->
                  [(AttrKey, (Object, SomeColumn))] ->
                  STM ()
                prepareSpecs specs [] =
                  runEdhTx ets $ colsExit $! reverse specs
                prepareSpecs
                  specs
                  ((!colKey, (_colObj, SomeColumn _ !col)) : rest) =
                    specifiedColWidth colKey $ \ !colWidth -> runEdhTx ets $
                      view'column'data col $ \(!cs, _cl) _ets -> do
                        let readCell !rowIdx !cellExit = do
                              !hvCell <- array'reader cs rowIdx
                              atomically $
                                runEdhTx ets $
                                  toEdh hvCell $
                                    \ !vCell -> edhValueStrTx vCell $
                                      \ !reprCell ->
                                        edhContIO $ cellExit reprCell
                        prepareSpecs
                          ((attrKeyStr colKey, colWidth, readCell) : specs)
                          rest

        !colKeys <- iopdKeys tcols
        runEdhTx ets $
          withTblCols tbl $
            prepareCols colKeys $ \ !colSpecs -> do
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
      \(Table _cv !rcv !tcols) !ets -> do
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
