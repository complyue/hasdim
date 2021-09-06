module Dim.Table where

-- import           Debug.Trace

import Control.Applicative
import Control.Concurrent.STM
import Control.Monad
import Control.Monad.IO.Class
import Data.Dynamic
import Data.Lossless.Decimal as D
import Data.Text (Text)
import qualified Data.Text as T
import Data.Unique
import qualified Data.Vector.Mutable as MV
import Dim.Column
import Dim.DataType
import Dim.InMem
import Dim.XCHG
import Language.Edh.MHI
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

withTable :: forall r. Object -> (Object -> Table -> Edh r) -> Edh r
withTable !obj !withTbl = do
  supers <- readTVarEdh $ edh'obj'supers obj
  withComposition $ obj : supers
  where
    withComposition :: [Object] -> Edh r
    withComposition [] = naM "not an expected Table object"
    withComposition (o : rest) = case fromDynamic =<< dynamicHostData o of
      Nothing -> withComposition rest
      Just (tbl :: Table) -> withTbl o tbl

withTblCols ::
  forall r. Table -> ([(AttrKey, Object, SomeColumn)] -> Edh r) -> Edh r
withTblCols (Table _cv _rcv !tcols) !withCols = do
  !colObjs <- iopdToListEdh tcols
  sequence (extractCol <$> colObjs) >>= withCols
  where
    extractCol ::
      (AttrKey, Object) -> Edh (AttrKey, Object, SomeColumn)
    extractCol (!colKey, !colObj) = withColumn colObj $
      \ !colInst !col -> return (colKey, colInst, col)

readTableRow :: Table -> Int -> Edh KwArgs
readTableRow tbl@(Table _cv !rcv _tcols) !i = do
  !rc <- readTVarEdh rcv
  !rowIdx <- regulateEdhIndexM rc i
  withTblCols tbl $ \ !cols -> do
    let readCell ::
          (AttrKey, Object, SomeColumn) ->
          Edh (AttrKey, EdhValue)
        readCell (colKey, _colInst, SomeColumn _ col) = do
          (cs, _cl) <- view'column'data col
          !hv <- liftIO $ array'reader cs rowIdx
          (colKey,) <$> toEdh hv
    odFromList <$> sequence (readCell <$> cols)

growTable :: ArrayCapacity -> Table -> Edh ()
growTable !newCap tbl@(Table cv rcv _tcols)
  | newCap <= 0 =
    throwEdhM UsageError $
      "you don't grow table capacity to " <> T.pack (show newCap)
  | otherwise = withTblCols tbl $ \ !cols -> do
    !cap <- readTVarEdh cv
    !rc <- readTVarEdh rcv
    -- if shrinking, update table capacity before updating any column
    -- so if it's to fail halfway we are still safe
    when (newCap < cap) $ writeTVarEdh cv newCap
    -- update row count now in case it's being shortened
    when (newCap < rc) $ writeTVarEdh rcv newCap
    -- now shrink all columns
    -- TODO do we need such a reusable utility `seqContIO` ?
    let growAll :: [(AttrKey, Object, SomeColumn)] -> Edh ()
        growAll [] = return ()
        growAll ((_, _, SomeColumn _ !col) : rest) = do
          void $ grow'column'capacity col newCap
          growAll rest
    growAll cols
    -- update table capacity after all columns successfully updated
    writeTVarEdh cv newCap

markTable :: ArrayLength -> Table -> Edh ()
markTable !newCnt tbl@(Table cv rcv _tcols) = withTblCols tbl $ \ !cols -> do
  !cap <- readTVarEdh cv
  if newCnt < 0 || newCnt > cap
    then
      throwEdhM UsageError $
        "table row count out of range: " <> T.pack (show newCnt) <> " vs "
          <> T.pack (show cap)
    else do
      !rc <- readTVarEdh rcv
      -- update row count now in case it's being shortened
      when (newCnt < rc) $ writeTVarEdh rcv newCnt
      -- now mark all columns
      liftIO $
        sequence_ $
          (<$> cols) $ \(_, _, SomeColumn _ !col) ->
            mark'column'length col newCnt
      -- update table row count after all columns successfully updated
      writeTVarEdh rcv newCnt

createTableClass :: Object -> Object -> Edh Object
createTableClass !dtBox !clsColumn =
  mkEdhClass "Table" (allocObjM tblAllocator) [] $ do
    !mths <-
      sequence $
        [ (AttrByName nm,) <$> mkEdhProc vc nm hp
          | (nm, vc, hp) <-
              [ ("__cap__", EdhMethod, wrapEdhProc tblCapProc),
                ("__len__", EdhMethod, wrapEdhProc tblLenProc),
                ("__grow__", EdhMethod, wrapEdhProc tblGrowProc),
                ("__mark__", EdhMethod, wrapEdhProc tblMarkRowCntProc),
                ("(@)", EdhMethod, wrapEdhProc tblAttrReadProc),
                ("(@=)", EdhMethod, wrapEdhProc tblAttrWriteProc),
                ("([])", EdhMethod, wrapEdhProc tblIdxReadProc),
                ("([=])", EdhMethod, wrapEdhProc tblIdxWriteProc),
                ("__repr__", EdhMethod, wrapEdhProc tblReprProc),
                ("__show__", EdhMethod, wrapEdhProc tblShowProc),
                ("__desc__", EdhMethod, wrapEdhProc tblDescProc)
              ]
        ]
          ++ [ (AttrByName nm,) <$> mkEdhProperty nm getter setter
               | (nm, getter, setter) <-
                   [ ("columns", tblColsGetterProc, Nothing)
                   ]
             ]
    !clsScope <- contextScope . edh'context <$> edhThreadState
    iopdUpdateEdh mths $ edh'scope'entity clsScope
  where
    tblAllocator ::
      "capacity" !: Int ->
      "row'count" ?: Int ->
      "columns" !: KeywordArgs ->
      ArgsPack -> -- allow/ignore arbitrary ctor args for descendant classes
      Edh (Maybe Unique, ObjectStore)
    tblAllocator
      (mandatoryArg -> !ctorCap)
      (defaultArg ctorCap -> !ctorCnt)
      (mandatoryArg -> KeywordArgs !colSpecs)
      _ctorOtherArgs
        | ctorCap <= 0 =
          throwEdhM UsageError $
            "table capacity should be a positive integer, not "
              <> T.pack (show ctorCap)
        | ctorCnt < 0 =
          throwEdhM UsageError $
            "table row count should be zero or a positive integer, not "
              <> T.pack (show ctorCnt)
        | otherwise =
          sequence (adaptColSpec <$> odToList colSpecs) >>= \ !ces -> do
            !cv <- newTVarEdh ctorCap
            !rcv <- newTVarEdh ctorCnt
            !tcols <- iopdFromListEdh ces
            return (Nothing, HostStore $ toDyn $ Table cv rcv tcols)
        where
          adaptColSpec ::
            (AttrKey, EdhValue) -> Edh (AttrKey, Object)
          adaptColSpec (colKey, colSpec) = case edhUltimate colSpec of
            EdhObject !obj -> do
              let tryCol =
                    withColumn obj $ \_colInst (SomeColumn _ !col) ->
                      view'column'data col >>= \(!cs, !cl) ->
                        if array'capacity cs < ctorCap || cl < ctorCnt
                          then
                            throwEdhM UsageError $
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
                            liftIO $ mark'column'length col ctorCnt
                            return (colKey, obj)

                  tryDt = withDataType obj $ \ !dt ->
                    createInMemColumn dt ctorCap ctorCnt >>= \ !col ->
                      (colKey,)
                        <$> createHostObjectM' clsColumn (toDyn col) [obj]

                  trySeq = case fromDynamic =<< dynamicHostData obj of
                    Nothing -> badSpec
                    Just (vec :: MV.IOVector EdhValue) ->
                      if MV.length vec < ctorCnt
                        then
                          throwEdhM UsageError $
                            "Sequence " <> attrKeyStr colKey
                              <> " is not long enough: "
                              <> T.pack (show $ MV.length vec)
                              <> " vs "
                              <> T.pack (show ctorCnt)
                        else do
                          -- todo should we copy the mutable IO vector?
                          !csv <- newTMVarEdh $ DirectArray vec
                          !clv <- newTVarEdh ctorCnt
                          (colKey,)
                            <$> createHostObjectM'
                              clsColumn
                              (toDyn $ someColumn $ InMemDirCol csv clv)
                              [dtBox]

              tryCol <|> tryDt <|> trySeq
            EdhArgsPack (ArgsPack !args !kwargs)
              | odNull kwargs ->
                (colKey,) <$> createBoxCol args
            EdhList (List _ !lv) ->
              readTVarEdh lv >>= \ !vs ->
                (colKey,) <$> createBoxCol vs
            -- TODO support range, slice, etc. w/ optional dtype
            _ -> badSpec
            where
              badSpec =
                edhSimpleDescM colSpec >>= \ !badDesc ->
                  throwEdhM UsageError $
                    "invalid column specification for "
                      <> attrKeyStr colKey
                      <> " - "
                      <> badDesc

          createBoxCol :: [EdhValue] -> Edh Object
          createBoxCol !es = do
            !iov <- liftIO $ do
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
              return iov
            !csv <- newTMVarEdh $ DirectArray iov
            !clv <- newTVarEdh ctorCnt
            createHostObjectM'
              clsColumn
              (toDyn $ someColumn $ InMemDirCol csv clv)
              [dtBox]

    withThisTable :: forall r. (Object -> Table -> Edh r) -> Edh r
    withThisTable !tblExit = do
      this <- edh'scope'this . contextScope . edh'context <$> edhThreadState
      case dynamicHostData this of
        Nothing ->
          throwEdhM EvalError "bug: not even a host value for Table"
        Just !dd -> case fromDynamic dd of
          Nothing ->
            throwEdhM EvalError $
              "bug: this is not a Table but " <> T.pack (show dd)
          Just !tbl -> tblExit this tbl

    tblColsGetterProc :: Edh EdhValue
    tblColsGetterProc = withThisTable $ \_this (Table _ _ !tcols) ->
      EdhArgsPack . ArgsPack [] . odTransform EdhObject
        <$> iopdSnapshotEdh tcols

    tblCapProc :: Edh EdhValue
    tblCapProc = withThisTable $ \_this (Table !cv _rcv _tcols) -> do
      !cap <- readTVarEdh cv
      return $ EdhDecimal $ fromIntegral cap

    tblLenProc :: Edh EdhValue
    tblLenProc = withThisTable $ \_this (Table _cv !rcv _tcols) -> do
      !rc <- readTVarEdh rcv
      return $ EdhDecimal $ fromIntegral rc

    tblGrowProc :: "newCap" !: Int -> Edh EdhValue
    tblGrowProc (mandatoryArg -> !newCap) = withThisTable $ \_this !tbl -> do
      growTable newCap tbl
      return nil

    tblMarkRowCntProc :: "newCnt" !: Int -> Edh EdhValue
    tblMarkRowCntProc (mandatoryArg -> !newCnt) = withThisTable $
      \_this !tbl -> do
        markTable newCnt tbl
        return nil

    tblAttrReadProc :: EdhValue -> Edh EdhValue
    tblAttrReadProc !keyVal = withThisTable $ \_this (Table _ _ !tcols) ->
      edhValueAsAttrKeyM keyVal >>= \ !attrKey ->
        iopdLookupEdh attrKey tcols >>= \case
          Nothing -> return edhNA
          Just !tcol -> return $ EdhObject tcol

    tblAttrWriteProc :: EdhValue -> "toVal" ?: EdhValue -> Edh EdhValue
    tblAttrWriteProc !attrKey (optionalArg -> !maybeAttrVal) =
      withThisTable $ \_this (Table !cv !rcv !tcols) ->
        edhValueAsAttrKeyM attrKey >>= \ !colKey -> case maybeAttrVal of
          Nothing -> do
            iopdDeleteEdh colKey tcols
            return nil
          Just !attrVal -> do
            !cap <- readTVarEdh cv
            !rc <- readTVarEdh rcv
            let badColSrc =
                  edhSimpleDescM attrVal >>= \ !badDesc ->
                    throwEdhM UsageError $
                      "not assignable to a table column: " <> badDesc
            case edhUltimate attrVal of
              EdhObject !obj -> do
                let tryCol =
                      withColumn obj $ \_colInst (SomeColumn _ !col) ->
                        view'column'data col >>= \(!cs, !cl) ->
                          if array'capacity cs < cap || cl < rc
                            then
                              throwEdhM UsageError $
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
                              liftIO $ mark'column'length col rc
                              iopdInsertEdh colKey obj tcols
                              return $ EdhObject obj

                    tryDt = withDataType obj $ \ !dt -> do
                      !col <- createInMemColumn dt cap rc
                      !colObj <- createHostObjectM' clsColumn (toDyn col) [obj]
                      iopdInsertEdh colKey colObj tcols
                      return $ EdhObject colObj

                    trySeq = case fromDynamic =<< dynamicHostData obj of
                      Nothing -> badColSrc
                      Just (vec :: MV.IOVector EdhValue) ->
                        if MV.length vec < rc
                          then
                            throwEdhM UsageError $
                              "Sequence " <> attrKeyStr colKey
                                <> " is not long enough: "
                                <> T.pack (show $ MV.length vec)
                                <> " vs "
                                <> T.pack (show rc)
                          else do
                            -- todo should we copy the mutable IO vector?
                            !csv <- newTMVarEdh $ DirectArray vec
                            !clv <- newTVarEdh rc
                            !colObj <-
                              createHostObjectM'
                                clsColumn
                                (toDyn $ someColumn $ InMemDirCol csv clv)
                                [dtBox]
                            iopdInsertEdh colKey colObj tcols
                            return $ EdhObject colObj

                tryCol <|> tryDt <|> trySeq
              _ -> badColSrc

    tblIdxReadProc :: EdhValue -> Edh EdhValue
    tblIdxReadProc !idxVal = withThisTable $
      \ !thisTbl !tbl -> withTblCols tbl $ \ !tcols -> do
        let withBoolIdx ::
              forall c f.
              ManagedColumn c f YesNo =>
              Object ->
              c YesNo ->
              Edh EdhValue
            withBoolIdx _ !idxCol = idxCols $ \ !thisCol !col ->
              extractColumnBool thisCol col idxCol
                >>= \(!newColObj, SomeColumn _ !newCol) ->
                  view'column'data newCol >>= \(!cs, !cl) ->
                    return (newColObj, array'capacity cs, cl)

            withIntpIdx ::
              forall c f.
              ManagedColumn c f Int =>
              Object ->
              c Int ->
              Edh EdhValue
            withIntpIdx _ !idxCol = idxCols $ \ !thisCol !col ->
              extractColumnFancy thisCol col idxCol
                >>= \(!newColObj, SomeColumn _ !newCol) ->
                  view'column'data newCol >>= \(!cs, !cl) ->
                    return (newColObj, array'capacity cs, cl)

            withEdhIdx :: Edh EdhValue
            withEdhIdx =
              parseEdhIndexM idxVal >>= \case
                Left !err -> throwEdhM UsageError err
                Right !idx -> case idx of
                  EdhIndex !i ->
                    EdhArgsPack . ArgsPack [] <$> readTableRow tbl i
                  EdhAny ->
                    EdhObject . edh'scope'that . contextScope . edh'context
                      <$> edhThreadState
                  EdhAll ->
                    EdhObject . edh'scope'that . contextScope . edh'context
                      <$> edhThreadState
                  EdhSlice !start !stop !step -> do
                    !rowCnt <- readTVarEdh (table'row'count tbl)
                    (!iStart, !iStop, !iStep) <-
                      regulateEdhSliceM rowCnt (start, stop, step)
                    idxCols $ \ !thisCol !col -> do
                      (!newColObj, SomeColumn _ !newCol) <-
                        sliceColumn thisCol col iStart iStop iStep
                      (!cs, !cl) <- view'column'data newCol
                      return (newColObj, array'capacity cs, cl)

            idxCols ::
              ( Object ->
                SomeColumn ->
                Edh (Object, ArrayCapacity, ArrayLength)
              ) ->
              Edh EdhValue
            idxCols doCol = do
              !rowCap <- readTVarEdh $ table'capacity tbl
              !rowCnt <- readTVarEdh $ table'row'count tbl
              let go ::
                    ArrayCapacity ->
                    ArrayLength ->
                    [(AttrKey, Object)] ->
                    [(AttrKey, Object, SomeColumn)] ->
                    Edh EdhValue
                  go !rowCap' !rowCnt' rCols [] = do
                    !cv' <- newTVarEdh rowCap'
                    !rcv' <- newTVarEdh rowCnt'
                    !tcols' <- iopdFromListEdh $ reverse rCols
                    !that <-
                      edh'scope'that . contextScope . edh'context
                        <$> edhThreadState
                    EdhObject
                      <$> mutCloneHostObjectM
                        that
                        thisTbl
                        (Table cv' rcv' tcols')
                  go
                    !rowCap'
                    !rowCnt'
                    rCols
                    ((!colKey, !colObj, !col) : rest) =
                      doCol colObj col >>= \(!colObj', cap', cl') ->
                        go
                          (min cap' rowCap')
                          (min cl' rowCnt')
                          ((colKey, colObj') : rCols)
                          rest
              go rowCap rowCnt [] tcols

        withColumnOf' @YesNo idxVal withBoolIdx
          <|> withColumnOf' @Int idxVal withIntpIdx
          <|> withEdhIdx

    tblIdxWriteProc :: EdhValue -> EdhValue -> Edh EdhValue
    tblIdxWriteProc !idxVal !toVal = withThisTable $
      \_this !tbl -> withTblCols tbl $ \ !tcols -> do
        let assignCols :: [(SomeColumn, EdhValue)] -> Edh EdhValue
            assignCols [] = return toVal
            assignCols ((!col, !tgtVal) : rest) = do
              idxAssignColumn col idxVal tgtVal
              assignCols rest

            matchColTgts :: [(AttrKey, Object, SomeColumn)] -> Edh EdhValue
            matchColTgts !cols = case edhUltimate toVal of
              -- assign with an apk
              EdhArgsPack (ArgsPack !tgts !kwtgts) ->
                matchApk [] cols tgts kwtgts
              EdhObject !obj -> (<|> broadcastMatch) $
                withTable obj $ \_ (Table _ _ !tcolsOther) -> do
                  -- todo validate shape match here?
                  !colsOther <- iopdSnapshotEdh tcolsOther
                  matchTbl [] cols colsOther
              _ -> broadcastMatch
              where
                broadcastMatch :: Edh EdhValue
                broadcastMatch =
                  assignCols $ (\(_, _, !col) -> (col, toVal)) <$> cols

                matchApk ::
                  [(SomeColumn, EdhValue)] ->
                  [(AttrKey, Object, SomeColumn)] ->
                  [EdhValue] ->
                  KwArgs ->
                  Edh EdhValue
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
                  Edh EdhValue
                matchTbl ms [] _ = assignCols $! reverse ms
                matchTbl ms ((!colKey, _colInst, !col) : rest) !colsOther =
                  case odLookup colKey colsOther of
                    Nothing -> matchTbl ms rest colsOther
                    Just !colOther ->
                      matchTbl
                        ((col, EdhObject colOther) : ms)
                        rest
                        colsOther

        matchColTgts tcols

    tblReprProc :: Edh EdhValue
    tblReprProc = withThisTable $ \_this (Table !cv !rcv !tcols) -> do
      !cap <- readTVarEdh cv
      !rc <- readTVarEdh rcv
      !tcl <- iopdToListEdh tcols
      let colShortRepr :: (AttrKey, Object) -> Edh Text
          colShortRepr (!colKey, !colObj) = do
            !dto <- getColumnDtype colObj
            withDataType dto $ \ !dt ->
              return $
                attrKeyStr colKey <> "= " <> data'type'ident dt <> ", "
      sequence (colShortRepr <$> tcl) >>= \ !colReprs ->
        return $
          EdhString $
            "Table( "
              <> T.pack (show cap)
              <> ", "
              <> T.pack (show rc)
              <> ", "
              <> T.concat colReprs
              <> ")"

    tblShowProc :: "columnWidth" ?: PackedArgs -> Edh EdhValue
    tblShowProc
      ( defaultArg (PackedArgs (ArgsPack [] odEmpty)) ->
          PackedArgs (ArgsPack !posWidth !kwWidth)
        ) = withThisTable $ \_this tbl@(Table _cv !rcv !tcols) -> do
        !rowCnt <- readTVarEdh rcv
        !colCnt <- iopdSizeEdh tcols
        !posColWidth <- newTVarEdh posWidth
        let specifiedColWidth :: AttrKey -> Edh Int
            specifiedColWidth !colKey = case odLookup colKey kwWidth of
              Just !cwv -> parseColWidth cwv
              Nothing ->
                readTVarEdh posColWidth >>= \case
                  [] -> return 10
                  [cwv] -> parseColWidth cwv
                  (cwv : rest) -> do
                    writeTVarEdh posColWidth rest
                    parseColWidth cwv
              where
                parseColWidth :: EdhValue -> Edh Int
                parseColWidth !cwVal = case edhUltimate cwVal of
                  EdhDecimal !d -> case D.decimalToInteger d of
                    Just !i | i > 0 && i < 2000 -> return $ fromInteger i
                    _ ->
                      edhValueDescM cwVal >>= \ !cwDesc ->
                        throwEdhM UsageError $
                          "invalid columnWidth: " <> cwDesc
                  _ ->
                    edhValueDescM cwVal >>= \ !cwDesc ->
                      throwEdhM UsageError $
                        "invalid columnWidth: " <> cwDesc

            prepareCols ::
              [(AttrKey, Object, SomeColumn)] ->
              Edh [(Text, Int, Int -> Edh Text)]
            prepareCols !cols =
              prepareSpecs [] cols
              where
                prepareSpecs ::
                  [(Text, Int, Int -> Edh Text)] ->
                  [(AttrKey, Object, SomeColumn)] ->
                  Edh [(Text, Int, Int -> Edh Text)]
                prepareSpecs specs [] = return $! reverse specs
                prepareSpecs
                  specs
                  ((!colKey, _colObj, SomeColumn _ !col) : rest) =
                    specifiedColWidth colKey >>= \ !colWidth -> do
                      (!cs, _cl) <- view'column'data col
                      let readCell !rowIdx = do
                            !hvCell <- liftIO $ array'reader cs rowIdx
                            !vCell <- toEdh hvCell
                            !reprCell <- edhValueStrM vCell
                            return reprCell

                      prepareSpecs
                        ( (attrKeyStr colKey, colWidth, readCell) :
                          specs
                        )
                        rest

        withTblCols tbl $ \ !cols -> do
          !colSpecs <- prepareCols cols
          let !titleLine =
                T.concat $
                  (<$> colSpecs) $ \(!title, !colWidth, _readCell) ->
                    centerBriefAlign (colWidth + 1) title
              !totalWidth = T.length titleLine
          let rowLine :: Int -> Edh Text
              rowLine !i = readCells "|" colSpecs
                where
                  readCells !line [] = return line
                  readCells !line ((_title, !colWidth, !readCell) : rest) =
                    readCell i >>= \ !cellStr ->
                      readCells
                        (line <> centerBriefAlign (colWidth + 1) cellStr)
                        rest
              rowLines :: [Int] -> Edh [Text]
              rowLines !rowIdxs = go [] rowIdxs
                where
                  go !rls [] = return $ reverse rls
                  go !rls (rowIdx : rest) =
                    rowLine rowIdx >>= \ !line -> go (line : rls) rest
              dataLines :: Edh [Text]
              dataLines =
                if rowCnt <= 20
                  then -- TODO make this tunable
                    rowLines [0 .. rowCnt - 1]
                  else
                    rowLines [0 .. 10] >>= \ !headLines ->
                      rowLines [rowCnt - 11 .. rowCnt - 1] >>= \ !tailLines ->
                        return $ headLines <> ["..."] <> tailLines
          !dls <- dataLines
          return $
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

    tblDescProc :: RestKwArgs -> Edh EdhValue
    tblDescProc !kwargs = withThisTable $ \_this (Table _cv !rcv !tcols) -> do
      !rowCnt <- readTVarEdh rcv
      !colCnt <- iopdSizeEdh tcols
      !cols <- iopdToListEdh tcols
      let tcDesc :: (AttrKey, Object) -> Edh Text
          tcDesc (!colKey, !colObj) =
            edhObjDescM' colObj kwargs >>= \ !colDesc ->
              return $
                " ** Table Column: "
                  <> T.pack (show colKey)
                  <> " :\n"
                  <> colDesc
      sequence (tcDesc <$> cols) >>= \ !tcDescLines ->
        return $
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
