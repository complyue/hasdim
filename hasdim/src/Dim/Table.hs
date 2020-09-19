
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

tableRowCount :: Table -> STM Int
tableRowCount (Table !trcv _) = readTMVar trcv

tableRowCapacity :: Table -> STM Int
tableRowCapacity (Table _ !cols) = iopdNull cols >>= \case
  True -> return 0
  False ->
    iopdValues cols
      >>= foldM (\ !cap !col -> min cap <$> colObjLen col) maxBound
 where
  colObjLen :: Object -> STM Int
  colObjLen !colObj = castObjectStore colObj >>= \case
    Just (_, col :: Column) -> columnCapacity col
    _                       -> error "bug: non-column object in table"

-- | the new row count must not be negative, and must not exceed the cap,
-- but it's not checked here, thus unsafe
unsafeMarkTableRowCount :: Int -> Table -> STM ()
unsafeMarkTableRowCount !rc (Table !trcv _) = do
  void $ tryTakeTMVar trcv
  void $ tryPutTMVar trcv rc

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
            $ [ (AttrByName nm, ) <$> mkHostProc clsScope vc nm hp
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
        iopdUpdate mths $ edh'scope'entity clsScope

 where

  -- | host constructor 
  --    Table(
  --       capacity, rowCount, 
  --       columns=(
  --         col1=<dtype> | <Column>, col2=...
  --       ),
  --    )
  tableAllocator
    :: "capacity" !: Int
    -> "columns" !: KeywordArgs
    -> "row'count" ?: Int
    -> ArgsPack -- allow/ignore arbitrary ctor args for descendant classes
    -> EdhObjectAllocator
  tableAllocator (mandatoryArg -> !ctorCap) (mandatoryArg  -> KeywordArgs  !colSpecs) (defaultArg ctorCap -> !rowCnt) _ctorOtherArgs !ctorExit !etsCtor
    = if ctorCap <= 0
      then
        throwEdh etsCtor UsageError
        $  "table capacity should be a positive integer, not "
        <> T.pack (show ctorCap)
      else if rowCnt < 0
        then
          throwEdh etsCtor UsageError
          $  "table row count should be zero or a positive integer, not "
          <> T.pack (show rowCnt)
        else odMapContSTM parseColSpec colSpecs $ \ !colCreators -> createTable
          etsCtor
          ctorCap
          rowCnt
          colCreators
          ((ctorExit . HostStore =<<) . newTVar . toDyn)
   where

    parseColSpec
      :: EdhValue
      -> ((Int -> TMVar Int -> (Object -> STM ()) -> STM ()) -> STM ())
      -> STM ()
    parseColSpec !val !exit = case edhUltimate val of
      EdhObject !obj -> castObjectStore obj >>= \case
        Just (!colThis, col :: Column) -> exit $ copyCol colThis obj col
        Nothing                        -> castObjectStore obj >>= \case
          Just (_, !dt) -> exit $ createCol dt
          Nothing ->
            throwEdh etsCtor UsageError
              $  "neither a Column object nor a dtype, but of class: "
              <> objClassName obj
      !badColSpec -> edhValueRepr etsCtor badColSpec $ \ !colRepr ->
        throwEdh etsCtor UsageError
          $  "invalid column specification, "
          <> T.pack (show $ edhTypeNameOf badColSpec)
          <> ": "
          <> colRepr

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
  tabIdxReadProc !idxVal !exit !ets =
    -- TODO impl. 
    exitEdh ets exit $ EdhString "<not impl.>"

  tabIdxWriteProc :: EdhValue -> EdhValue -> EdhHostProc
  tabIdxWriteProc !idxVal !toVal !exit !ets =
    -- TODO impl. 
    exitEdh ets exit $ EdhString "<not impl.>"


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
          Just (!colThis, Column !dt !clv !csv) -> do
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
                edhCloneHostObj ets colThis colObj tcol $ \ !newColObj ->
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

  tabShowProc :: RestKwArgs -> EdhHostProc
  tabShowProc !kwargs !exit !ets =
    withThisHostObj' ets (exitEdh ets exit $ EdhString "<bogus-Table>")
      $ \_hsv tab@(Table !trcv !tcols) ->
          let
            parseTabTitle :: (Text -> STM ()) -> EdhValue -> STM ()
            parseTabTitle !exit' = \case
              EdhString !title -> exit' title
              !titleVal -> edhValueRepr ets titleVal $ \ !title -> exit' title
            parseColWidth :: (Int -> STM ()) -> EdhValue -> STM ()
            parseColWidth !exit' = \case
              EdhDecimal !cwNum -> case D.decimalToInteger cwNum of
                Just !cw | cw > 0 && cw < 200 -> exit' $ fromInteger cw
                _ ->
                  throwEdh ets UsageError $ "invalid columnWidth: " <> T.pack
                    (show cwNum)
              !badColWidthVal ->
                edhValueRepr ets badColWidthVal $ \ !badColWidth ->
                  throwEdh ets UsageError
                    $  "invalid columnWidth: "
                    <> badColWidth
          in
            odLookupContSTM 10 (flip parseColWidth) (AttrByName "cw") kwargs
              $ \ !colWidth ->
                  odLookupContSTM "table"
                                  (flip parseTabTitle)
                                  (AttrByName "title")
                                  kwargs
                    $ \ !tabTitle -> do
                        !tcc        <- iopdSize tcols
                        !trc        <- readTMVar trcv
                        !cap        <- tableRowCapacity tab
                        !colEntries <- iopdToList tcols
                        let !titleLine =
                              T.concat
                                $   centerBriefAlign colWidth
                                .   T.pack
                                .   show
                                .   fst
                                <$> colEntries
                            !totalWidth = T.length titleLine
                        exitEdh ets exit
                          $  EdhString
                          $  T.replicate (totalWidth + 1) "-"
                          <> "\n|"
                          <> centerBriefAlign
                               totalWidth
                               (  tabTitle
                               <> " "
                               <> T.pack (show trc)
                               <> "/"
                               <> T.pack (show cap)
                               <> " * "
                               <> T.pack (show tcc)
                               )
                          <> "\n|"
                          <> T.replicate (totalWidth - 1) "-"
                          <> "|\n|"
                          <> titleLine
                          <> "\n|"
                          <> T.replicate (totalWidth - 1) "-"
                          <> "|\n|"

  -- TODO fill here with column data
                          <> centerBriefAlign totalWidth "..."

                          <> "\n"
                          <> T.replicate (totalWidth + 1) "-"


  tabDescProc :: EdhHostProc
  tabDescProc !exit !ets =
    withThisHostObj' ets (exitEdh ets exit $ EdhString "<bogus-Table>")
      $ \_hsv tab@(Table !trcv !tcols) -> do
          !trc <- readTMVar trcv
          exitEdh ets exit
            $  EdhString
            $  "table:\n * Row Count: "
            <> T.pack (show trc)
  -- TODO fill here with column statistics
            <> "...\n"


centerBriefAlign :: Int -> Text -> Text
centerBriefAlign !colWidth !txt | colWidth <= 5 = T.take colWidth txt
centerBriefAlign !colWidth !txt                 = if len < colWidth
  then
    let (!margin, !rightPadding) = quotRem (colWidth - len) 2
    in  T.pack (replicate margin ' ')
        <> txt
        <> T.pack (replicate (margin - 1 + rightPadding) ' ')
        <> "|"
  else T.take (colWidth - 4) txt <> "...|"
  where !len = T.length txt

