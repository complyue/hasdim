
module Dim.Table where

import           Prelude
-- import           Debug.Trace

-- import           Unsafe.Coerce
import           GHC.Conc                       ( unsafeIOToSTM )

import           Foreign                 hiding ( void )

import           Control.Monad
-- import           Control.Monad.Reader

import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import qualified Data.Text                     as T

import qualified Data.Vector.Mutable           as MV

import           Data.Dynamic

import           Data.Lossless.Decimal         as D

import           Language.Edh.EHI
import           Language.Edh.Batteries

import           Dim.DataType
import           Dim.Column


data Table = Table {
    -- this is also the mutex to coordinate concurrent modifications to the
    -- table
    table'row'count :: !(TMVar Int)
    -- underlying table storage, represented as column objects, those sharing
    -- a common length, which is the row count
  , table'columns :: !(IOPD AttrKey Object)
  }

castTableColumn :: Object -> STM Column
castTableColumn !colObj = castObjectStore colObj >>= \case
  Nothing        -> error "bug: non-column object in a table"
  Just (_, !col) -> return col

castTableColumn' :: Object -> STM (Object, Column)
castTableColumn' !colObj = castObjectStore colObj >>= \case
  Nothing               -> error "bug: non-column object in a table"
  Just (!thisCol, !col) -> return (thisCol, col)

tableRowCount :: Table -> STM Int
tableRowCount (Table !trcv _) = readTMVar trcv

tableRowCapacity :: Table -> STM Int
tableRowCapacity (Table _ !tcols) = iopdNull tcols >>= \case
  True -> return 0
  False ->
    iopdValues tcols
      >>= foldM
            (\ !cap !col -> min cap <$> (columnCapacity =<< castTableColumn col)
            )
            maxBound

-- | the new row count must not be negative, and must not exceed the cap,
-- but it's not checked here, thus unsafe
unsafeMarkTableRowCount :: Int -> Table -> STM ()
unsafeMarkTableRowCount !rc (Table !trcv _) = do
  void $ tryTakeTMVar trcv
  void $ tryPutTMVar trcv rc


readTableRow :: EdhThreadState -> Table -> Int -> (ArgsPack -> STM ()) -> STM ()
readTableRow !ets (Table !trcVar !tcols) !i !exit =
  readTMVar trcVar >>= \ !trc -> edhRegulateIndex ets trc i $ \ !rowIdx -> do
    let readCols !cells [] = exit $ ArgsPack [] $ odFromList $ reverse cells
        readCols !cells ((!k, !colObj) : rest) =
          castTableColumn colObj >>= \ !col ->
            unsafeReadColumnCell ets col rowIdx
              $ \ !cellVal -> readCols ((k, cellVal) : cells) rest
    iopdToList tcols >>= readCols []


createTable
  :: EdhThreadState
  -> Int
  -> Int
  -> OrderedDict
       AttrKey
       (Int -> TMVar Int -> (Object -> STM ()) -> STM ())
  -> (Table -> STM ())
  -> STM ()
createTable _ets !cap !rowCnt !colCreators !exit = do
  !trcv <- newTMVar rowCnt
  seqcontSTM
      [ \ !exit' -> colCreator cap trcv $ \ !col -> exit' (key, col)
      | (!key, !colCreator) <- odToList colCreators
      ]
    $ \ !colEntries ->
        iopdFromList colEntries >>= \ !tcols -> exit $ Table trcv tcols

growTable :: EdhThreadState -> Int -> Table -> STM () -> STM ()
growTable _ets !newRowCnt (Table !trcv !tcols) !exit =
  iopdValues tcols >>= \ !cols -> do
    !trc <- takeTMVar trcv

    sequence_ $ growCol <$> cols

    putTMVar trcv $ min newRowCnt trc

    exit
 where
  growCol :: Object -> STM ()
  growCol !col = castObjectStore col >>= \case
    Nothing                     -> error "bug: non-column obj in table"
    Just (_, Column !dt _ !csv) -> do
      !cs  <- readTVar csv
      !cs' <- flat'grow'array dt cs newRowCnt
      writeTVar csv cs'


createTableClass :: Object -> Scope -> STM Object
createTableClass !colClass !clsOuterScope =
  mkHostClass clsOuterScope "Table" (allocEdhObj tableAllocator) []
    $ \ !clsScope -> do
        !mths <-
          sequence
          $  [ (AttrByName nm, ) <$> mkHostProc clsScope vc nm hp
             | (nm, vc, hp) <-
               [ ("__cap__" , EdhMethod, wrapHostProc tabCapProc)
               , ("__grow__", EdhMethod, wrapHostProc tabGrowProc)
               , ("__len__" , EdhMethod, wrapHostProc tabLenProc)
               , ("__mark__", EdhMethod, wrapHostProc tabMarkRowCntProc)
               , ("[]"      , EdhMethod, wrapHostProc tabIdxReadProc)
               , ("[=]"     , EdhMethod, wrapHostProc tabIdxWriteProc)
               , ("@"       , EdhMethod, wrapHostProc tabAttrReadProc)
               , ("@="      , EdhMethod, wrapHostProc tabAttrWriteProc)
               , ("__repr__", EdhMethod, wrapHostProc tabReprProc)
               , ("__show__", EdhMethod, wrapHostProc tabShowProc)
               , ("__desc__", EdhMethod, wrapHostProc tabDescProc)
               ]
             ]
          ++ [ (AttrByName nm, ) <$> mkHostProperty clsScope nm getter setter
             | (nm, getter, setter) <- [("columns", tabColsGetterProc, Nothing)]
             ]
        iopdUpdate mths $ edh'scope'entity clsScope

 where

  dtBox = makeHostDataType @EdhValue "box" edhNA

  -- | host constructor 
  --    Table(
  --       capacity,
  --       columns=(
  --         col1=<dtype> | <Column>, col2=...
  --       ), row'count, 
  --    )
  tableAllocator
    :: "capacity" !: Int
    -> "columns" !: KeywordArgs
    -> "row'count" ?: Int
    -> ArgsPack -- allow/ignore arbitrary ctor args for descendant classes
    -> EdhObjectAllocator
  tableAllocator (mandatoryArg -> !ctorCap) (mandatoryArg  -> KeywordArgs  !colSpecs) (defaultArg ctorCap -> !rowCnt) _ctorOtherArgs !ctorExit !etsCtor
    | ctorCap <= 0
    = throwEdh etsCtor UsageError
      $  "table capacity should be a positive integer, not "
      <> T.pack (show ctorCap)
    | rowCnt < 0
    = throwEdh etsCtor UsageError
      $  "table row count should be zero or a positive integer, not "
      <> T.pack (show rowCnt)
    | otherwise
    = odMapContSTM' parseColSpec colSpecs $ \ !colCreators -> createTable
      etsCtor
      ctorCap
      rowCnt
      colCreators
      ((ctorExit . HostStore =<<) . newTVar . toDyn)
   where

    parseColSpec
      :: (AttrKey, EdhValue)
      -> ((Int -> TMVar Int -> (Object -> STM ()) -> STM ()) -> STM ())
      -> STM ()
    parseColSpec (!key, !val) !exit = case edhUltimate val of
      EdhObject !obj -> castObjectStore obj >>= \case
        Just (!thisCol, col :: Column) -> exit $ copyCol thisCol obj col
        Nothing                        -> castObjectStore obj >>= \case
          Just (_, !dt) -> exit $ createCol dt
          Nothing ->
            throwEdh etsCtor UsageError
              $  attrKeyStr key
              <> " is neither a Column nor a dtype object, but of class: "
              <> objClassName obj
      EdhArgsPack (ArgsPack !args !kwargs) | odNull kwargs ->
        exit $ boxCol args
      !badColSpec -> edhValueDesc etsCtor badColSpec $ \ !badDesc ->
        throwEdh etsCtor UsageError
          $  "invalid column specification for "
          <> attrKeyStr key
          <> " - "
          <> badDesc

    boxCol :: [EdhValue] -> Int -> TMVar Int -> (Object -> STM ()) -> STM ()
    boxCol !items !cap !clv !exit = do
      !ha <- unsafeIOToSTM $ do
        !ha <- MV.unsafeNew cap
        let fill i _ | i >= cap = return ha
            fill i []           = do
              MV.set (MV.unsafeSlice i (cap - i) ha) edhNA
              return ha
            fill i (item : rest) = do
              MV.write ha i item
              fill (i + 1) rest
        fill 0 items
      !csv <- newTVar $ HostArray @EdhValue cap ha
      let !col = Column dtBox clv csv
      edhCreateHostObj colClass (toDyn col) [] >>= exit

    createCol :: DataType -> Int -> TMVar Int -> (Object -> STM ()) -> STM ()
    createCol !dt !cap !clv !exit = createColumn etsCtor dt cap clv
      $ \ !col -> edhCreateHostObj colClass (toDyn col) [] >>= exit

    copyCol
      :: Object
      -> Object
      -> Column
      -> Int
      -> TMVar Int
      -> (Object -> STM ())
      -> STM ()
    copyCol !fromThis !fromThat (Column !dti !clvSrc !csvSrc) !cap !clv !exit =
      do
        !clSrc <- readTMVar clvSrc
        readTVar csvSrc >>= \case
          DeviceArray _capSrc !fp -> do
            !cs' <- unsafeIOToSTM $ do
              !p'  <- callocArray cap
              !fp' <- newForeignPtr finalizerFree p'
              withForeignPtr fp $ \ !p -> copyArray p' p $ min cap clSrc
              return $ DeviceArray cap fp'
            !csv' <- newTVar cs'
            edhCloneHostObj etsCtor fromThis fromThat (Column dti clv csv') exit
          HostArray _capSrc !ha -> do
            !cs' <- unsafeIOToSTM $ do
              !ha' <- MV.new cap
              let !cpLen = min cap clSrc
                  !tgt   = MV.unsafeSlice 0 cpLen ha'
                  !src   = MV.unsafeSlice 0 cpLen ha
              MV.unsafeCopy tgt src
              return $ HostArray cap ha'
            !csv' <- newTVar cs'
            edhCloneHostObj etsCtor fromThis fromThat (Column dti clv csv') exit


  tabGrowProc :: "newCap" !: Int -> EdhHostProc
  tabGrowProc (mandatoryArg -> !newCap) !exit !ets = if newCap <= 0
    then throwEdh ets UsageError "table capacity must be a positive integer"
    else withThisHostObj ets $ \_hsv !tab ->
      growTable ets newCap tab
        $ exitEdh ets exit
        $ EdhObject
        $ edh'scope'that
        $ contextScope
        $ edh'context ets

  tabCapProc :: EdhHostProc
  tabCapProc !exit !ets = withThisHostObj ets $ \_hsv !tab ->
    tableRowCapacity tab
      >>= \ !cap -> exitEdh ets exit $ EdhDecimal $ fromIntegral cap

  tabLenProc :: EdhHostProc
  tabLenProc !exit !ets = withThisHostObj ets $ \_hsv !tab -> tableRowCount tab
    >>= \ !len -> exitEdh ets exit $ EdhDecimal $ fromIntegral len

  tabMarkRowCntProc :: "newLen" !: Int -> EdhHostProc
  tabMarkRowCntProc (mandatoryArg -> !newLen) !exit !ets =
    withThisHostObj ets $ \_hsv !tab -> do
      !cap <- tableRowCapacity tab
      if newLen >= 0 && newLen <= fromIntegral cap
        then unsafeMarkTableRowCount newLen tab >> exitEdh ets exit nil
        else throwEdh ets UsageError "table length out of range"


  tabIdxReadProc :: EdhValue -> EdhHostProc
  tabIdxReadProc !idxVal !exit !ets = withThisHostObj ets $ \_hsv !tab ->
    castObjectStore' idxVal >>= \case
      Just (_, !idxCol) ->
        case data'type'identifier $ column'data'type idxCol of
          "yesno" -> do -- yesno index 
            !trcVarNew <- newEmptyTMVar
            !tcolsNew  <- iopdEmpty
            let
              extractCols [] =
                edhCloneHostObj ets thisTab thatTab (Table trcVarNew tcolsNew)
                  $ \ !newTabObj -> exitEdh ets exit $ EdhObject newTabObj
              extractCols ((!key, !thatCol) : rest) =
                castTableColumn' thatCol >>= \(!thisCol, !col) ->
                  extractColumnBool' trcVarNew ets idxCol col (extractCols rest)
                    $ \ !colNew ->
                        edhCloneHostObj ets thisCol thatCol colNew
                          $ \ !newColObj -> do
                              iopdInsert key newColObj tcolsNew
                              extractCols rest
            iopdToList (table'columns tab) >>= extractCols
          "intp" -> do -- fancy index 
            !trcVarNew <- newEmptyTMVar
            !tcolsNew  <- iopdEmpty
            let
              extractCols [] =
                edhCloneHostObj ets thisTab thatTab (Table trcVarNew tcolsNew)
                  $ \ !newTabObj -> exitEdh ets exit $ EdhObject newTabObj
              extractCols ((!key, !thatCol) : rest) =
                castTableColumn' thatCol >>= \(!thisCol, !col) ->
                  extractColumnFancy' trcVarNew
                                      ets
                                      idxCol
                                      col
                                      (extractCols rest)
                    $ \ !colNew ->
                        edhCloneHostObj ets thisCol thatCol colNew
                          $ \ !newColObj -> do
                              iopdInsert key newColObj tcolsNew
                              extractCols rest
            iopdToList (table'columns tab) >>= extractCols
          !badDti ->
            throwEdh ets UsageError
              $  "invalid dtype="
              <> badDti
              <> " for a column as an index to a table"
      Nothing -> parseEdhIndex ets idxVal $ \case
        Left !err -> throwEdh ets UsageError err
        Right (EdhIndex !i) ->
          readTableRow ets tab i $ exitEdh ets exit . EdhArgsPack
        Right EdhAny -> exitEdh ets exit $ EdhObject thatTab
        Right EdhAll -> exitEdh ets exit $ EdhObject thatTab
        Right (EdhSlice !start !stop !step) -> do
          !trc <- tableRowCount tab
          edhRegulateSlice ets trc (start, stop, step)
            $ \(!iStart, !iStop, !iStep) -> do
                !trcVarNew <- newEmptyTMVar
                !tcolsNew  <- iopdEmpty
                let sliceCols [] =
                      edhCloneHostObj ets
                                      thisTab
                                      thatTab
                                      (Table trcVarNew tcolsNew)
                        $ \ !newTabObj -> exitEdh ets exit $ EdhObject newTabObj
                    sliceCols ((!key, !thatCol) : rest) =
                      castTableColumn' thatCol >>= \(!thisCol, !col) ->
                        unsafeSliceColumn' trcVarNew col iStart iStop iStep
                          $ \ !colNew ->
                              edhCloneHostObj ets thisCol thatCol colNew
                                $ \ !newColObj -> do
                                    iopdInsert key newColObj tcolsNew
                                    sliceCols rest
                iopdToList (table'columns tab) >>= sliceCols
   where
    !thisTab = edh'scope'this $ contextScope $ edh'context ets
    !thatTab = edh'scope'that $ contextScope $ edh'context ets


  tabIdxWriteProc :: EdhValue -> EdhValue -> EdhHostProc
  tabIdxWriteProc !idxVal !toVal !exit !ets =
    withThisHostObj ets $ \_hsv (Table !trcv !tcols) -> readTMVar trcv
      >>= \ !trc -> iopdToList tcols >>= matchColTgts trc assignCols
   where
    assignCols :: [(Object, EdhValue)] -> STM ()
    assignCols [] = exitEdh ets exit toVal
    assignCols ((!colObj, !tgtVal) : rest) =
      castTableColumn colObj >>= \ !col ->
        runEdhTx ets $ idxAssignColumn col idxVal tgtVal $ \_ _ets ->
          assignCols rest

    matchColTgts
      :: Int
      -> ([(Object, EdhValue)] -> STM ())
      -> [(AttrKey, Object)]
      -> STM ()
    matchColTgts !trc !mcExit !cols = case edhUltimate toVal of
      -- assign with an apk
      EdhArgsPack (ArgsPack !tgts !kwtgts) -> matchApk [] cols tgts kwtgts
      !toVal'                              -> castObjectStore' toVal' >>= \case
        -- assign with another table 
        Just (_tabOther, Table !trcvOther !tcolsOther) -> do
          !trcOther <- readTMVar trcvOther
          if trc /= trcOther
            then
              throwEdh ets UsageError
              $  "table row count mismatch: "
              <> T.pack (show trc)
              <> " vs "
              <> T.pack (show trcOther)
            else iopdSnapshot tcolsOther >>= matchTab [] cols
        -- assign with a scalar
        Nothing -> mcExit $ (, toVal) . snd <$> cols
     where
      matchApk
        :: [(Object, EdhValue)]
        -> [(AttrKey, Object)]
        -> [EdhValue]
        -> KwArgs
        -> STM ()
      matchApk !ms [] _ _ = mcExit $! reverse ms
      matchApk !ms ((!colKey, !colObj) : rest) !tgts !kwtgts =
        case odLookup colKey kwtgts of
          Just !tgtVal -> matchApk ((colObj, tgtVal) : ms) rest tgts kwtgts
          Nothing      -> case tgts of
            [] -> matchApk ms rest [] kwtgts
            tgtVal : tgts' ->
              matchApk ((colObj, tgtVal) : ms) rest tgts' kwtgts

      matchTab
        :: [(Object, EdhValue)]
        -> [(AttrKey, Object)]
        -> OrderedDict AttrKey Object
        -> STM ()
      matchTab !ms [] _ = mcExit $! reverse ms
      matchTab !ms ((!colKey, !colObj) : rest) !colsOther =
        case odLookup colKey colsOther of
          Nothing -> matchTab ms rest colsOther
          Just !colOther ->
            matchTab ((colObj, EdhObject colOther) : ms) rest colsOther


  tabColsGetterProc :: EdhHostProc
  tabColsGetterProc !exit !ets =
    withThisHostObj ets $ \_hsv (Table _ !tcols) ->
      iopdSnapshot tcols >>= \ !tcols' ->
        exitEdh ets exit $ EdhArgsPack $ ArgsPack [] $ odTransform EdhObject
                                                                   tcols'

  tabAttrReadProc :: EdhValue -> EdhHostProc
  tabAttrReadProc !keyVal !exit !ets =
    withThisHostObj ets $ \_hsv (Table _ !tcols) ->
      edhValueAsAttrKey ets keyVal $ \ !attrKey ->
        iopdLookup attrKey tcols >>= \case
          Nothing    -> exitEdh ets exit edhNA
          Just !tcol -> exitEdh ets exit $ EdhObject tcol

  tabAttrWriteProc :: EdhValue -> "toVal" ?: EdhValue -> EdhHostProc
  tabAttrWriteProc !attrKey (optionalArg -> !maybeAttrVal) !exit !ets =
    withThisHostObj ets $ \_hsv tab@(Table !trcv !tcols) -> case maybeAttrVal of
      Nothing -> edhValueAsAttrKey ets attrKey $ \ !key -> iopdDelete key tcols
      Just !attrVal -> case edhUltimate attrVal of
        EdhObject !colObj -> castObjectStore colObj >>= \case
          Nothing                               -> badCol attrVal
          Just (!thisCol, Column !dt !clv !csv) -> do
            !cl  <- readTMVar clv
            !trc <- readTMVar trcv
            if cl < trc
              then
                throwEdh ets UsageError
                $  "no enough data in column: column length "
                <> T.pack (show cl)
                <> " vs table row count "
                <> T.pack (show trc)
              else do
                !tcap <- tableRowCapacity tab
                !ca   <- readTVar csv
                !tca  <- unsafeIOToSTM $ dupFlatArray ca cl tcap
                !tcol <- Column dt trcv <$> newTVar tca
                edhCloneHostObj ets thisCol colObj tcol $ \ !newColObj ->
                  edhValueAsAttrKey ets attrKey $ \ !key -> do
                    iopdInsert key newColObj tcols
                    exitEdh ets exit $ EdhObject newColObj
        _ -> badCol attrVal
   where
    badCol !badVal = edhValueDesc ets badVal $ \ !badValDesc ->
      throwEdh ets UsageError
        $  "can only set column(s) to a table, not "
        <> badValDesc


  tabReprProc :: EdhHostProc
  tabReprProc !exit !ets =
    withThisHostObj' ets (exitEdh ets exit $ EdhString "<bogus-Table>")
      $ \_hsv tab@(Table !trcv !tcols) -> do
          !trc <- readTMVar trcv
          !cap <- tableRowCapacity tab
          (fmap colShortRepr <$> iopdToList tcols >>=)
            $ flip seqcontSTM
            $ \ !colReprs ->
                exitEdh ets exit
                  $  EdhString
                  $  "Table( "
                  <> T.pack (show cap)
                  <> ", "
                  <> T.pack (show trc)
                  <> ", "
                  <> T.concat colReprs
                  <> ")"
   where
    colShortRepr :: (AttrKey, Object) -> (Text -> STM ()) -> STM ()
    -- TODO better repr here
    colShortRepr (!colKey, !colObj) !exit' = castObjectStore colObj >>= \case
      Nothing -> throwEdh ets EvalError "bug: non-column object in table"
      Just (_, Column !dt _ _) ->
        exit' $ T.pack (show colKey) <> "=" <> data'type'identifier dt <> ", "


  tabShowProc :: "columnWidth" ?: PackedArgs -> EdhHostProc
  tabShowProc (defaultArg (PackedArgs (ArgsPack [] odEmpty)) -> PackedArgs (ArgsPack !posWidth !kwWidth)) !exit !ets
    = withThisHostObj' ets (exitEdh ets exit $ EdhString "<bogus-Table>")
      $ \_hsv (Table !trcv !tcols) -> prepareCols tcols $ \ !colSpecs -> do
          !tcc <- iopdSize tcols
          !trc <- readTMVar trcv
          let !titleLine =
                T.concat $ (<$> colSpecs) $ \(!title, !colWidth, _cellRdr) ->
                  centerBriefAlign (colWidth + 1) $ title
              !totalWidth = T.length titleLine
          let
            rowLine :: Int -> (Text -> STM ()) -> STM ()
            rowLine !i !rowLineExit = readCells "|" colSpecs
             where
              readCells !line [] = rowLineExit line
              readCells !line ((_title, !colWidth, !cellRdr) : rest) =
                cellRdr i $ \ !cellVal ->
                  edhValueStr ets cellVal
                    $ \ !cellStr -> readCells
                        (line <> centerBriefAlign (colWidth + 1) cellStr)
                        rest
            rowLines :: [Int] -> ([Text] -> STM ()) -> STM ()
            rowLines !rowIdxs !rowLinesExit = go [] rowIdxs
             where
              go !rls [] = rowLinesExit $ reverse rls
              go !rls (rowIdx : rest) =
                rowLine rowIdx $ \ !line -> go (line : rls) rest
            dataLines :: ([Text] -> STM ()) -> STM ()
            dataLines !dataLinesExit = if trc <= 20
              -- TODO make this tunable
              then rowLines [0 .. trc - 1] dataLinesExit
              else rowLines [0 .. 10] $ \ !headLines ->
                rowLines [trc - 11 .. trc - 1] $ \ !tailLines ->
                  dataLinesExit $ headLines <> ["..."] <> tailLines
          dataLines $ \ !dls ->
            exitEdh ets exit
              $  EdhString
              $  T.replicate (totalWidth + 1) "-"
              <> "\n|"
              <> centerBriefAlign
                   totalWidth
                   (  "table of "
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
    prepareCols
      :: IOPD AttrKey Object
      -> (  [(Text -- ^ column title
                  , Int -- ^ display width 
                          -- | cell reader
                       , Int -> (EdhValue -> STM ()) -> STM ())]
         -> STM ()
         )
      -> STM ()
    prepareCols !tcols !colsExit =
      iopdToList tcols >>= prepareSpecs [] posWidth kwWidth
     where
      prepareSpecs
        :: [(Text, Int, Int -> (EdhValue -> STM ()) -> STM ())]
        -> [EdhValue]
        -> KwArgs
        -> [(AttrKey, Object)]
        -> STM ()
      prepareSpecs !specs _ _ [] = colsExit $! reverse specs
      prepareSpecs !specs !pos'w !kw'w ((!colKey, !colObj) : rest) = do
        (Column !dt _clv !csv) <- castTableColumn colObj
        !cs                    <- readTVar csv
        let !title   = attrKeyStr colKey
            !cellRdr = flat'array'read dt ets cs
        case odTakeOut colKey kw'w of
          (Just !cwVal, !kw'w') -> parseColWidth cwVal $ \ !colWidth ->
            prepareSpecs ((title, colWidth, cellRdr) : specs) pos'w kw'w' rest
          (Nothing, !kw'w') -> case pos'w of
            [] -> prepareSpecs ((title, 10, cellRdr) : specs) pos'w kw'w' rest
            [!cwVal] -> parseColWidth cwVal $ \ !colWidth -> prepareSpecs
              ((title, colWidth, cellRdr) : specs)
              pos'w
              kw'w'
              rest
            cwVal : pos'w' -> parseColWidth cwVal $ \ !colWidth ->
              prepareSpecs ((title, colWidth, cellRdr) : specs)
                           pos'w'
                           kw'w'
                           rest
      parseColWidth :: EdhValue -> (Int -> STM ()) -> STM ()
      parseColWidth !cwVal !cwExit = case edhUltimate cwVal of
        EdhDecimal !d -> case D.decimalToInteger d of
          Just !i | i > 0 && i < 2000 -> cwExit $ fromInteger i
          _                           -> edhValueDesc ets cwVal $ \ !cwDesc ->
            throwEdh ets UsageError $ "invalid columnWidth: " <> cwDesc
        _ -> edhValueDesc ets cwVal $ \ !cwDesc ->
          throwEdh ets UsageError $ "invalid columnWidth: " <> cwDesc


  tabDescProc :: RestKwArgs -> EdhHostProc
  tabDescProc !kwargs !exit !ets =
    withThisHostObj' ets (exitEdh ets exit $ EdhString "<bogus-Table>")
      $ \_hsv (Table !trcv !tcols) ->
          (fmap tcDesc <$> iopdToList tcols >>=)
            $ flip seqcontSTM
            $ \ !tcDescLines -> do
                !trc <- readTMVar trcv
                exitEdh ets exit
                  $  EdhString
                  $  " * table row count: "
                  <> T.pack (show trc)
                  <> "\n"
                  <> T.unlines tcDescLines
   where
    tcDesc :: (AttrKey, Object) -> (Text -> STM ()) -> STM ()
    tcDesc (!colKey, !colObj) !exit' =
      runEdhTx ets $ descProc (EdhObject colObj) kwargs $ \ !colDescVal _ets ->
        edhValueStr ets colDescVal $ \ !colDesc ->
          exit'
            $  " * table column "
            <> T.pack (show colKey)
            <> " :\n"
            <> colDesc


centerBriefAlign :: Int -> Text -> Text
centerBriefAlign !dispWidth !txt | dispWidth < 4 =
  let !txt' = T.take dispWidth txt
      !len  = T.length txt'
  in  if len < dispWidth
        then txt' <> T.replicate (dispWidth - len) " "
        else txt'
centerBriefAlign !dispWidth !txt = if len < dispWidth
  then
    let (!margin, !rightPadding) = quotRem (dispWidth - len) 2
    in  T.replicate margin " "
        <> txt
        <> T.replicate (margin - 1 + rightPadding) " "
        <> "|"
  else T.take (dispWidth - 4) txt <> "...|"
  where !len = T.length txt

