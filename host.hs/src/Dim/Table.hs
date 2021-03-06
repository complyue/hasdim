module Dim.Table where

-- import           Debug.Trace

-- import           Unsafe.Coerce

import Control.Concurrent.STM
  ( STM,
    TVar,
    newTVar,
    readTVar,
    writeTVar,
  )
import Data.Dynamic (toDyn)
import Data.Lossless.Decimal as D (decimalToInteger)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Vector.Mutable as MV
import Dim.ColArts
import Dim.Column
import Dim.DataType
import Dim.InMem
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.Batteries (descProc)
import Language.Edh.EHI
import Prelude

data Table = Table
  { -- capacity allocated for number of rows, i.e. capacity of each column
    table'row'capacity :: !(TVar Int),
    -- valid number of rows in this table
    table'row'count :: !(TVar Int),
    -- underlying table storage, represented as column objects
    --
    -- grow/change of row capacity/count will be propagated to all these
    -- column objects, as column capacity/length
    table'columns :: !(IOPD AttrKey Object)
  }

castTableColumn :: Object -> STM Column
castTableColumn !colObj =
  castObjectStore colObj >>= \case
    Nothing -> error "bug: non-column object in a table"
    Just (_, !col) -> return col

castTableColumn' :: Object -> STM (Object, Column)
castTableColumn' !colObj =
  castObjectStore colObj >>= \case
    Nothing -> error "bug: non-column object in a table"
    Just (!thisCol, !col) -> return (thisCol, col)

readTableRow :: EdhThreadState -> Table -> Int -> (ArgsPack -> STM ()) -> STM ()
readTableRow !ets (Table _trCapV !trCntV !tcols) !i !exit =
  readTVar trCntV >>= \ !trCnt -> edhRegulateIndex ets trCnt i $ \ !rowIdx -> do
    let readCols !cells [] = exit $ ArgsPack [] $ odFromList $ reverse cells
        readCols !cells ((!k, !colObj) : rest) =
          castTableColumn colObj >>= \ !col ->
            unsafeReadColumnCell ets col rowIdx $
              \ !cellVal -> readCols ((k, cellVal) : cells) rest
    iopdToList tcols >>= readCols []

createTable ::
  EdhThreadState ->
  Int ->
  Int ->
  OrderedDict AttrKey (Int -> Int -> (Object -> STM ()) -> STM ()) ->
  (Table -> STM ()) ->
  STM ()
createTable _ets !trCap !trCnt !colCreators !exit = do
  !trCapV <- newTVar trCap
  !trCntV <- newTVar trCnt
  seqcontSTM
    [ \ !exit' -> colCreator trCap trCnt $ \ !colObj -> exit' (key, colObj)
      | (!key, !colCreator) <- odToList colCreators
    ]
    $ \ !colEntries ->
      iopdFromList colEntries
        >>= \ !tcols -> exit $ Table trCapV trCntV tcols

growTable :: EdhThreadState -> Int -> Table -> STM () -> STM ()
growTable !ets !newRowCap (Table !trCapV !trCntV !tcols) !exit =
  iopdValues tcols >>= growCols
  where
    doneGrown :: STM ()
    doneGrown = do
      writeTVar trCapV newRowCap

      -- update row count, necessary in case it's actually shrinked
      !trCnt <- readTVar trCntV
      writeTVar trCntV $ min newRowCap trCnt

      exit

    growCols :: [Object] -> STM ()
    growCols [] = doneGrown
    growCols (colObj : rest) = grow1 colObj $ growCols rest

    grow1 :: Object -> STM () -> STM ()
    grow1 !colObj !growExit =
      castObjectStore colObj >>= \case
        Nothing -> error "bug: non-column obj in table"
        Just (_, Column !col) ->
          runEdhTx ets $ grow'column'capacity col newRowCap $ const growExit

createTableClass :: Object -> Scope -> STM Object
createTableClass !colClass !clsOuterScope =
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
    dtBox = makeHostDataType @EdhValue "box" edhNA

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
              castObjectStore obj >>= \case
                Just (_, col'@(Column !col)) -> do
                  !cc <- columnCapacity col'
                  !cl <- read'column'length col
                  if cl < ctorCnt || cc < ctorCap
                    then
                      throwEdh etsCtor UsageError $
                        "column "
                          <> attrKeyStr key
                          <> " is too short: "
                          <> T.pack (show cl)
                          <> "/"
                          <> T.pack (show cc)
                          <> " vs "
                          <> T.pack (show ctorCnt)
                          <> "/"
                          <> T.pack (show ctorCap)
                    else
                      runEdhTx etsCtor $
                        mark'column'length col ctorCnt $
                          exit $
                            containCol obj
                Nothing ->
                  castObjectStore obj >>= \case
                    Just (_, !dt) -> exit $ createCol dt
                    Nothing ->
                      throwEdh etsCtor UsageError $
                        attrKeyStr key
                          <> " is neither a Column nor a dtype object, but of class: "
                          <> objClassName obj
            EdhArgsPack (ArgsPack !args !kwargs)
              | odNull kwargs ->
                exit $ boxCol args
            !badColSpec -> edhValueDesc etsCtor badColSpec $ \ !badDesc ->
              throwEdh etsCtor UsageError $
                "invalid column specification for "
                  <> attrKeyStr key
                  <> " - "
                  <> badDesc

          boxCol :: [EdhValue] -> Int -> Int -> (Object -> STM ()) -> STM ()
          boxCol !items !cap !len !exit = do
            !ha <- unsafeIOToSTM $ do
              !ha <- MV.unsafeNew cap
              let fill i _ | i >= cap = return ha
                  fill i [] = do
                    MV.set (MV.unsafeSlice i (cap - i) ha) edhNA
                    return ha
                  fill i (item : rest) = do
                    MV.write ha i item
                    fill (i + 1) rest
              fill 0 items
            !csv <- newTVar $ HostArray @EdhValue cap ha
            !clv <- newTVar len
            let !col = Column $ InMemColumn dtBox csv clv
            edhCreateHostObj colClass col >>= exit

          createCol :: DataType -> Int -> Int -> (Object -> STM ()) -> STM ()
          createCol !dt !cap !len !exit =
            runEdhTx etsCtor $
              createInMemColumn dt cap len $ \ !col ->
                edhCreateHostObj colClass col >>= exit

          containCol :: Object -> Int -> Int -> (Object -> STM ()) -> STM ()
          containCol !colObj _cap _len !exit = exit colObj

    tabGrowProc :: "newCap" !: Int -> EdhHostProc
    tabGrowProc (mandatoryArg -> !newCap) !exit !ets =
      if newCap <= 0
        then throwEdh ets UsageError "table capacity must be a positive integer"
        else withThisHostObj ets $ \ !tab ->
          growTable ets newCap tab $
            exitEdh ets exit $
              EdhObject $
                edh'scope'that $
                  contextScope $
                    edh'context ets

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
          else
            let markColsLen :: [Object] -> STM ()
                markColsLen [] = do
                  writeTVar trCntV newLen
                  exitEdh ets exit nil
                markColsLen (colObj : rest) =
                  castTableColumn colObj >>= \(Column !col) ->
                    runEdhTx ets $
                      mark'column'length col newLen $ markColsLen rest
             in iopdValues tcols >>= markColsLen

    tabIdxReadProc :: EdhValue -> EdhHostProc
    tabIdxReadProc !idxVal !exit !ets =
      withThisHostObj ets $ \tab@(Table _trCapV !trCntV !tcols) ->
        castObjectStore' idxVal >>= \case
          Just (_, idxCol'@(Column !idxCol)) ->
            case data'type'identifier $ data'type'of'column idxCol of
              "yesno" -> do
                -- yesno index
                !rtrCapV <- newTVar =<< read'column'length idxCol
                !rtrCntV <- newTVar 0
                !tcolsNew <- iopdEmpty
                let extractCols [] =
                      edhCloneHostObj
                        ets
                        thisTab
                        thatTab
                        (Table rtrCapV rtrCntV tcolsNew)
                        $ \ !newTabObj -> exitEdh ets exit $ EdhObject newTabObj
                    extractCols ((!key, !thatCol) : rest) =
                      extractColumnBool ets thatCol idxCol' (extractCols rest) $
                        \ !clNew !newColObj -> do
                          writeTVar rtrCntV clNew
                          iopdInsert key newColObj tcolsNew
                          extractCols rest
                iopdToList tcols >>= extractCols
              "intp" -> do
                -- fancy index
                !rtrCapV <- newTVar =<< read'column'length idxCol
                !rtrCntV <- newTVar =<< read'column'length idxCol
                !tcolsNew <- iopdEmpty
                let extractCols [] =
                      edhCloneHostObj
                        ets
                        thisTab
                        thatTab
                        (Table rtrCapV rtrCntV tcolsNew)
                        $ \ !newTabObj -> exitEdh ets exit $ EdhObject newTabObj
                    extractCols ((!key, !thatCol) : rest) =
                      extractColumnFancy
                        ets
                        thatCol
                        idxCol'
                        (extractCols rest)
                        $ \ !newColObj -> do
                          iopdInsert key newColObj tcolsNew
                          extractCols rest
                iopdToList tcols >>= extractCols
              !badDti ->
                throwEdh ets UsageError $
                  "invalid dtype="
                    <> badDti
                    <> " for a column as an index to a table"
          Nothing -> parseEdhIndex ets idxVal $ \case
            Left !err -> throwEdh ets UsageError err
            Right (EdhIndex !i) ->
              readTableRow ets tab i $ exitEdh ets exit . EdhArgsPack
            Right EdhAny -> exitEdh ets exit $ EdhObject thatTab
            Right EdhAll -> exitEdh ets exit $ EdhObject thatTab
            Right (EdhSlice !start !stop !step) -> do
              !trCnt <- readTVar trCntV
              edhRegulateSlice ets trCnt (start, stop, step) $
                \(!iStart, !iStop, !iStep) -> do
                  !rtrCapV <- newTVar 0
                  !rtrCntV <- newTVar 0
                  !tcolsNew <- iopdEmpty
                  let sliceCols [] =
                        edhCloneHostObj
                          ets
                          thisTab
                          thatTab
                          (Table rtrCapV rtrCntV tcolsNew)
                          $ \ !newTabObj ->
                            exitEdh ets exit $
                              EdhObject newTabObj
                      sliceCols ((!key, !thatCol) : rest) =
                        sliceColumn ets thatCol iStart iStop iStep $
                          \ !ccNew !clNew !newColObj -> do
                            writeTVar rtrCapV ccNew
                            writeTVar rtrCntV clNew
                            iopdInsert key newColObj tcolsNew
                            sliceCols rest
                  iopdToList tcols >>= sliceCols
      where
        !thisTab = edh'scope'this $ contextScope $ edh'context ets
        !thatTab = edh'scope'that $ contextScope $ edh'context ets

    tabIdxWriteProc :: EdhValue -> EdhValue -> EdhHostProc
    tabIdxWriteProc !idxVal !toVal !exit !ets =
      withThisHostObj ets $ \(Table _trCapV !trCntV !tcols) ->
        readTVar trCntV
          >>= \ !trCnt -> iopdToList tcols >>= matchColTgts trCnt assignCols
      where
        assignCols :: [(Object, EdhValue)] -> STM ()
        assignCols [] = exitEdh ets exit toVal
        assignCols ((!colObj, !tgtVal) : rest) =
          castTableColumn colObj >>= \ !col ->
            runEdhTx ets $
              idxAssignColumn col idxVal tgtVal $ \_ _ets ->
                assignCols rest

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
                castObjectStore obj >>= \case
                  Just (_, col'@(Column !col)) -> do
                    !cc <- columnCapacity col'
                    !cl <- read'column'length col
                    if cl < trCnt || cc < trCap
                      then
                        throwEdh ets UsageError $
                          "column not long enough: "
                            <> T.pack (show cl)
                            <> "/"
                            <> T.pack (show cc)
                            <> " vs "
                            <> T.pack (show trCnt)
                            <> "/"
                            <> T.pack (show trCap)
                      else runEdhTx ets $
                        mark'column'length col trCnt $ do
                          iopdInsert key obj tcols
                          exitEdh ets exit attrVal
                  Nothing ->
                    castObjectStore obj >>= \case
                      Just (_, !dt) ->
                        runEdhTx ets $
                          createInMemColumn dt trCap trCnt $ \ !col -> do
                            !newColObj <-
                              edhCreateHostObj colClass col
                            iopdInsert key newColObj tcols
                            exitEdh ets exit $ EdhObject newColObj
                      Nothing -> badColSrc attrVal
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
          castObjectStore colObj >>= \case
            Nothing -> throwEdh ets EvalError "bug: non-column object in table"
            Just (_, Column !col) ->
              exit' $
                T.pack (show colKey)
                  <> "="
                  <> data'type'identifier (data'type'of'column col)
                  <> ", "

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
              prepareSpecs !specs !pos'w !kw'w ((!colKey, !colObj) : rest) = do
                (Column !col) <- castTableColumn colObj
                !cs <- view'column'data col
                let !title = attrKeyStr colKey
                    !cellRdr = flat'array'read (data'type'of'column col) ets cs
                case odTakeOut colKey kw'w of
                  (Just !cwVal, !kw'w') -> parseColWidth cwVal $ \ !colWidth ->
                    prepareSpecs
                      ((title, colWidth, cellRdr) : specs)
                      pos'w
                      kw'w'
                      rest
                  (Nothing, !kw'w') -> case pos'w of
                    [] ->
                      prepareSpecs
                        ((title, 10, cellRdr) : specs)
                        pos'w
                        kw'w'
                        rest
                    [!cwVal] -> parseColWidth cwVal $ \ !colWidth ->
                      prepareSpecs
                        ((title, colWidth, cellRdr) : specs)
                        pos'w
                        kw'w'
                        rest
                    cwVal : pos'w' -> parseColWidth cwVal $ \ !colWidth ->
                      prepareSpecs
                        ((title, colWidth, cellRdr) : specs)
                        pos'w'
                        kw'w'
                        rest
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
