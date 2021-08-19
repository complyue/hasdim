module Dim.Table where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Monad
import Data.Dynamic
import Data.Lossless.Decimal as D
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Vector.Mutable as MV
import Dim.ColArts
import Dim.Column
import Dim.DataType
import Dim.InMem
import Dim.XCHG
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.Batteries
import Language.Edh.EHI
import Type.Reflection
import Prelude

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

withTableSelf :: (Object -> Table -> EdhTx) -> EdhTx
withTableSelf !tblExit !ets = do
  supers <- readTVar $ edh'obj'supers that
  withComposition $ that : supers
  where
    that = edh'scope'that $ contextScope $ edh'context ets
    naExit = throwEdh ets UsageError "not an expected self Table"

    withComposition :: [Object] -> STM ()
    withComposition [] = naExit
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
growTable !newRowCap tbl@(Table cv rcv _tcols) !exit =
  withTblCols tbl $ \ !cols !ets -> do
    !cap <- readTVar cv
    !rc <- readTVar rcv
    -- if shrinking, update table capacity before updating any column
    -- so if it's to fail halfway we are still safe
    when (newRowCap < cap) $ writeTVar cv newRowCap
    -- update row count in case it's actually shrinked
    when (newRowCap < rc) $ writeTVar rcv newRowCap
    -- now shrink all columns
    runEdhTx ets $
      seqEdhTx (grow1 . snd <$> cols) $ \_ _ets -> do
        -- update table capacity after all columns successfully updated
        writeTVar cv newRowCap
        exitEdh ets exit ()
  where
    grow1 :: SomeColumn -> EdhTxExit () -> EdhTx
    grow1 (SomeColumn _ !col) = grow'column'capacity col newRowCap

createTable ::
  EdhThreadState ->
  ArrayCapacity ->
  ArrayLength ->
  OrderedDict
    AttrKey
    (ArrayCapacity -> ArrayLength -> (Object -> STM ()) -> STM ()) ->
  (Table -> STM ()) ->
  STM ()
createTable _ets !cap !rc !colCreators !exit = do
  !cv <- newTVar cap
  !rcv <- newTVar rc
  seqcontSTM
    [ \ !exit' -> colCreator cap rc $ \ !colObj -> exit' (key, colObj)
      | (!key, !colCreator) <- odToList colCreators
    ]
    $ \ !colEntries -> iopdFromList colEntries >>= exit . Table cv rcv

createTableClass :: Object -> Object -> Scope -> STM Object
createTableClass !dtBox !colClass !clsOuterScope =
  mkHostClass clsOuterScope "Table" (allocEdhObj tableAllocator) [] $
    \ !clsScope -> do
      !mths <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc clsScope vc nm hp
            | (nm, vc, hp) <-
                [ ("__cap__", EdhMethod, wrapHostProc tabCapProc),
                  ("__grow__", EdhMethod, wrapHostProc tabGrowProc),
                  ("__len__", EdhMethod, wrapHostProc tabLenProc),
                  ("__mark__", EdhMethod, wrapHostProc tabMarkRowCntProc),
                  ("([])", EdhMethod, wrapHostProc tabIdxReadProc),
                  ("([=])", EdhMethod, wrapHostProc tabIdxWriteProc),
                  ("(@)", EdhMethod, wrapHostProc tabAttrReadProc),
                  ("(@=)", EdhMethod, wrapHostProc tabAttrWriteProc),
                  ("__repr__", EdhMethod, wrapHostProc tabReprProc),
                  ("__show__", EdhMethod, wrapHostProc tabShowProc),
                  ("__desc__", EdhMethod, wrapHostProc tabDescProc)
                ]
          ]
            ++ [ (AttrByName nm,) <$> mkHostProperty clsScope nm getter setter
                 | (nm, getter, setter) <-
                     [ ("columns", tabColsGetterProc, Nothing)
                     ]
               ]
      iopdUpdate mths $ edh'scope'entity clsScope
  where
    tableAllocator ::
      "capacity" !: Int ->
      "row'count" ?: Int ->
      "columns" !: KeywordArgs ->
      ArgsPack -> -- allow/ignore arbitrary ctor args for descendant classes
      EdhObjectAllocator
    tableAllocator
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
        | otherwise =
          odMapContSTM' parseColSpec colSpecs $ \ !colCreators ->
            createTable etsCtor ctorCap ctorCnt colCreators $
              ctorExit Nothing . HostStore . toDyn
        where
          parseColSpec ::
            (AttrKey, EdhValue) ->
            ((Int -> Int -> (Object -> STM ()) -> STM ()) -> STM ()) ->
            STM ()
          parseColSpec (!key, !val) !exit = case edhUltimate val of
            EdhObject !obj ->
              undefined
            -- withColumn' obj tryDt $ \_colInst col ->
            -- do
            --   !cc <- colu col'
            --   !cl <- read'column'length col
            --   if cl < ctorCnt || cc < ctorCap
            --     then
            --       throwEdh etsCtor UsageError $
            --         "column "
            --           <> attrKeyStr key
            --           <> " is too short: "
            --           <> T.pack (show cl)
            --           <> "/"
            --           <> T.pack (show cc)
            --           <> " vs "
            --           <> T.pack (show ctorCnt)
            --           <> "/"
            --           <> T.pack (show ctorCap)
            --     else
            --       runEdhTx etsCtor $
            --         mark'column'length col ctorCnt $
            --           exit $  containCol obj

            -- castObjectStore obj >>= \case
            --   Just (_, !dt) -> exit $ createCol dt
            --   Nothing ->
            --     throwEdh etsCtor UsageError $
            --       attrKeyStr key
            --         <> " is neither a Column nor a dtype object, but of class: "
            --         <> objClassName obj
            EdhArgsPack (ArgsPack !args !kwargs)
              | odNull kwargs ->
                exit $ boxCol args
            !badColSpec -> edhSimpleDesc etsCtor badColSpec $ \ !badDesc ->
              throwEdh etsCtor UsageError $
                "invalid column specification for "
                  <> attrKeyStr key
                  <> " - "
                  <> badDesc

          boxCol :: [EdhValue] -> Int -> Int -> (Object -> STM ()) -> STM ()
          boxCol !items !cap !len !exit = do
            undefined
          -- !ha <- unsafeIOToSTM $ do
          --   !ha <- MV.unsafeNew cap
          --   let fill i _ | i >= cap = return ha
          --       fill i [] = do
          --         MV.set (MV.unsafeSlice i (cap - i) ha) edhNA
          --         return ha
          --       fill i (item : rest) = do
          --         MV.write ha i item
          --         fill (i + 1) rest
          --   fill 0 items
          -- !csv <- newTVar $ DirectArray @EdhValue cap ha
          -- !clv <- newTVar len
          -- let !col = someColumn $ InMemColumn dtBox csv clv
          -- edhCreateHostObj colClass col >>= exit

          -- createCol :: DataType a -> Int -> Int -> (Object -> STM ()) -> STM ()
          -- createCol !dt !cap !len !exit =
          --   runEdhTx etsCtor $
          --     createInMemColumn dt cap len $ \ !col ->
          --       edhCreateHostObj colClass col >>= exit

          containCol :: Object -> Int -> Int -> (Object -> STM ()) -> STM ()
          containCol !colObj _cap _len !exit = exit colObj

    tabGrowProc :: "newCap" !: Int -> EdhHostProc
    tabGrowProc (mandatoryArg -> !newCap) !exit =
      if newCap <= 0
        then throwEdhTx UsageError "table capacity must be a positive integer"
        else withTableSelf $ \_tblInst !tbl ->
          growTable newCap tbl $ exit . const nil

    tabCapProc :: EdhHostProc
    tabCapProc !exit !ets =
      withThisHostObj ets $ \(Table !trCapV _trCntV _tcols) ->
        readTVar trCapV
          >>= \ !trCap -> exitEdh ets exit $ EdhDecimal $ fromIntegral trCap

    tabLenProc :: EdhHostProc
    tabLenProc !exit !ets =
      withThisHostObj ets $ \(Table _trCapV !trCntV _tcols) ->
        readTVar trCntV
          >>= \ !trCnt -> exitEdh ets exit $ EdhDecimal $ fromIntegral trCnt

    tabMarkRowCntProc :: "newLen" !: Int -> EdhHostProc
    tabMarkRowCntProc (mandatoryArg -> !newLen) !exit !ets =
      withThisHostObj ets $ \(Table !trCapV !trCntV !tcols) -> do
        !cap <- readTVar trCapV
        if newLen < 0 || newLen > fromIntegral cap
          then throwEdh ets UsageError "table length out of range"
          else undefined
    -- let markColsLen :: [Object] -> STM ()
    --     markColsLen [] = do
    --       writeTVar trCntV newLen
    --       exitEdh ets exit nil
    --     markColsLen (colObj : rest) =
    --       runEdhTx ets $
    --         withColumn colObj $ \_colInst !col ->
    --           mark'column'length col newLen $ markColsLen rest
    --  in iopdValues tcols >>= markColsLen

    tabIdxReadProc :: EdhValue -> EdhHostProc
    tabIdxReadProc !idxVal !exit !ets =
      undefined
    -- withThisHostObj ets $ \tab@(Table _trCapV !trCntV !tcols) ->
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
    --         readTableRow ets tab i $ exitEdh ets exit . EdhArgsPack
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

    tabIdxWriteProc :: EdhValue -> EdhValue -> EdhHostProc
    tabIdxWriteProc !idxVal !toVal !exit !ets =
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
              Just (_tabOther, Table _trCapV !trCntVOther !tcolsOther) -> do
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

    tabColsGetterProc :: EdhHostProc
    tabColsGetterProc !exit !ets = withThisHostObj ets $ \(Table _ _ !tcols) ->
      iopdSnapshot tcols >>= \ !tcols' ->
        exitEdh ets exit $
          EdhArgsPack $
            ArgsPack [] $
              odTransform
                EdhObject
                tcols'

    tabAttrReadProc :: EdhValue -> EdhHostProc
    tabAttrReadProc !keyVal !exit !ets =
      withThisHostObj ets $ \(Table _ _ !tcols) ->
        edhValueAsAttrKey ets keyVal $ \ !attrKey ->
          iopdLookup attrKey tcols >>= \case
            Nothing -> exitEdh ets exit edhNA
            Just !tcol -> exitEdh ets exit $ EdhObject tcol

    tabAttrWriteProc :: EdhValue -> "toVal" ?: EdhValue -> EdhHostProc
    tabAttrWriteProc !attrKey (optionalArg -> !maybeAttrVal) !exit !ets =
      edhValueAsAttrKey ets attrKey $ \ !key ->
        withThisHostObj ets $ \(Table !trCapV !trCntV !tcols) -> do
          !trCap <- readTVar trCapV
          !trCnt <- readTVar trCntV
          case maybeAttrVal of
            Nothing -> iopdDelete key tcols
            Just !attrVal -> case edhUltimate attrVal of
              EdhObject !obj ->
                undefined
              -- withColumn obj $ \_colInst !col -> do
              -- castObjectStore obj >>= \case
              --   Just (_, col'@(Column !col)) -> do
              --     !cc <- columnCapacity col'
              --     !cl <- read'column'length col
              --     if cl < trCnt || cc < trCap
              --       then
              --         throwEdh ets UsageError $
              --           "column not long enough: "
              --             <> T.pack (show cl)
              --             <> "/"
              --             <> T.pack (show cc)
              --             <> " vs "
              --             <> T.pack (show trCnt)
              --             <> "/"
              --             <> T.pack (show trCap)
              --       else runEdhTx ets $
              --         mark'column'length col trCnt $ do
              --           iopdInsert key obj tcols
              --           exitEdh ets exit attrVal
              --   Nothing ->
              --     castObjectStore obj >>= \case
              --       Just (_, !dt) ->
              --         runEdhTx ets $
              --           createInMemColumn dt trCap trCnt $ \ !col -> do
              --             !newColObj <-
              --               edhCreateHostObj colClass col
              --             iopdInsert key newColObj tcols
              --             exitEdh ets exit $ EdhObject newColObj
              --       Nothing -> badColSrc attrVal
              _ -> badColSrc attrVal
      where
        badColSrc !badVal = edhValueDesc ets badVal $ \ !badValDesc ->
          throwEdh ets UsageError $
            "can only set a column or a dtype to a table, not "
              <> badValDesc

    tabReprProc :: EdhHostProc
    tabReprProc !exit !ets =
      withThisHostObj' ets (exitEdh ets exit $ EdhString "<bogus-Table>") $
        \(Table !trCapV !trCntV !tcols) -> do
          !trCap <- readTVar trCapV
          !trCnt <- readTVar trCntV
          (fmap colShortRepr <$> iopdToList tcols >>=) $
            flip seqcontSTM $
              \ !colReprs ->
                exitEdh ets exit $
                  EdhString $
                    "Table( "
                      <> T.pack (show trCap)
                      <> ", "
                      <> T.pack (show trCnt)
                      <> ", "
                      <> T.concat colReprs
                      <> ")"
      where
        colShortRepr :: (AttrKey, Object) -> (Text -> STM ()) -> STM ()
        -- TODO better repr here
        colShortRepr (!colKey, !colObj) !exit' =
          undefined
    -- withColumn colObj $ \_colInst !col ->
    --   exit' $
    --     T.pack (show colKey)
    --       <> "="
    --       <> data'type'identifier (data'type'of'column col)
    --       <> ", "

    tabShowProc :: "columnWidth" ?: PackedArgs -> EdhHostProc
    tabShowProc
      ( defaultArg (PackedArgs (ArgsPack [] odEmpty)) ->
          PackedArgs (ArgsPack !posWidth !kwWidth)
        )
      !exit
      !ets =
        withThisHostObj' ets (exitEdh ets exit $ EdhString "<bogus-Table>") $
          \(Table _trCapV !trCntV !tcols) ->
            prepareCols tcols $ \ !colSpecs -> do
              !tcc <- iopdSize tcols
              !trc <- readTVar trCntV
              let !titleLine =
                    T.concat $
                      (<$> colSpecs) $ \(!title, !colWidth, _cellRdr) ->
                        centerBriefAlign (colWidth + 1) $ title
                  !totalWidth = T.length titleLine
              let rowLine :: Int -> (Text -> STM ()) -> STM ()
                  rowLine !i !rowLineExit = readCells "|" colSpecs
                    where
                      readCells !line [] = rowLineExit line
                      readCells !line ((_title, !colWidth, !cellRdr) : rest) =
                        cellRdr i $ \ !cellVal ->
                          edhValueStr ets cellVal $
                            \ !cellStr ->
                              readCells
                                ( line
                                    <> centerBriefAlign (colWidth + 1) cellStr
                                )
                                rest
                  rowLines :: [Int] -> ([Text] -> STM ()) -> STM ()
                  rowLines !rowIdxs !rowLinesExit = go [] rowIdxs
                    where
                      go !rls [] = rowLinesExit $ reverse rls
                      go !rls (rowIdx : rest) =
                        rowLine rowIdx $ \ !line -> go (line : rls) rest
                  dataLines :: ([Text] -> STM ()) -> STM ()
                  dataLines !dataLinesExit =
                    if trc <= 20
                      then -- TODO make this tunable
                        rowLines [0 .. trc - 1] dataLinesExit
                      else rowLines [0 .. 10] $ \ !headLines ->
                        rowLines [trc - 11 .. trc - 1] $ \ !tailLines ->
                          dataLinesExit $ headLines <> ["..."] <> tailLines
              dataLines $ \ !dls ->
                exitEdh ets exit $
                  EdhString $
                    T.replicate (totalWidth + 1) "-"
                      <> "\n|"
                      <> centerBriefAlign
                        totalWidth
                        ( "table of "
                            <> T.pack (show tcc)
                            <> " columns * "
                            <> T.pack (show trc)
                            <> " rows"
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
        where
          prepareCols ::
            IOPD AttrKey Object ->
            ( [ ( Text,
                  Int,
                  Int -> (EdhValue -> STM ()) -> STM ()
                )
              ] ->
              STM ()
            ) ->
            STM ()
          prepareCols !tcols !colsExit =
            iopdToList tcols >>= prepareSpecs [] posWidth kwWidth
            where
              prepareSpecs ::
                [(Text, Int, Int -> (EdhValue -> STM ()) -> STM ())] ->
                [EdhValue] ->
                KwArgs ->
                [(AttrKey, Object)] ->
                STM ()
              prepareSpecs !specs _ _ [] = colsExit $! reverse specs
              prepareSpecs !specs !pos'w !kw'w ((!colKey, !colObj) : rest) =
                undefined
              -- withColumn colObj $ \_colInst !col -> do
              -- !cs <- view'column'data col
              -- let !title = attrKeyStr colKey
              --     !cellRdr = flat'array'read (data'type'of'column col) ets cs
              -- case odTakeOut colKey kw'w of
              --   (Just !cwVal, !kw'w') -> parseColWidth cwVal $ \ !colWidth ->
              --     prepareSpecs
              --       ((title, colWidth, cellRdr) : specs)
              --       pos'w
              --       kw'w'
              --       rest
              --   (Nothing, !kw'w') -> case pos'w of
              --     [] ->
              --       prepareSpecs
              --         ((title, 10, cellRdr) : specs)
              --         pos'w
              --         kw'w'
              --         rest
              --     [!cwVal] -> parseColWidth cwVal $ \ !colWidth ->
              --       prepareSpecs
              --         ((title, colWidth, cellRdr) : specs)
              --         pos'w
              --         kw'w'
              --         rest
              --     cwVal : pos'w' -> parseColWidth cwVal $ \ !colWidth ->
              --       prepareSpecs
              --         ((title, colWidth, cellRdr) : specs)
              --         pos'w'
              --         kw'w'
              --         rest
              parseColWidth :: EdhValue -> (Int -> STM ()) -> STM ()
              parseColWidth !cwVal !cwExit = case edhUltimate cwVal of
                EdhDecimal !d -> case D.decimalToInteger d of
                  Just !i | i > 0 && i < 2000 -> cwExit $ fromInteger i
                  _ -> edhValueDesc ets cwVal $ \ !cwDesc ->
                    throwEdh ets UsageError $ "invalid columnWidth: " <> cwDesc
                _ -> edhValueDesc ets cwVal $ \ !cwDesc ->
                  throwEdh ets UsageError $ "invalid columnWidth: " <> cwDesc

    tabDescProc :: RestKwArgs -> EdhHostProc
    tabDescProc !kwargs !exit !ets =
      withThisHostObj' ets (exitEdh ets exit $ EdhString "<bogus-Table>") $
        \(Table _trCapV !trCntV !tcols) ->
          (fmap tcDesc <$> iopdToList tcols >>=) $
            flip seqcontSTM $
              \ !tcDescLines -> do
                !trc <- readTVar trCntV
                exitEdh ets exit $
                  EdhString $
                    " * table row count: "
                      <> T.pack (show trc)
                      <> "\n"
                      <> T.unlines tcDescLines
      where
        tcDesc :: (AttrKey, Object) -> (Text -> STM ()) -> STM ()
        tcDesc (!colKey, !colObj) !exit' =
          runEdhTx ets $
            descProc (LitExpr $ ValueLiteral $ EdhObject colObj) kwargs $
              \ !colDescVal _ets -> edhValueStr ets colDescVal $ \ !colDesc ->
                exit' $
                  " * table column "
                    <> T.pack (show colKey)
                    <> " :\n"
                    <> colDesc

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
