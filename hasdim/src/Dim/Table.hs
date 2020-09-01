
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

import           Data.Coerce
import           Data.Dynamic

import           Data.Lossless.Decimal         as D

import           Language.Edh.EHI

import           Dim.DataType
import           Dim.Column


data Table = Table {
    -- this is also the mutex to coordinate concurrent modifications to the
    -- table
    table'row'count :: !(TMVar Int)
    -- underlying table storage, represented as columns, those sharing 
  , table'columns :: !(IOPD AttrKey Column)
    -- optional labels associated with each row
  , table'row'labels :: !(Maybe EdhVector)
    -- labels associated with each column, default to their respective index
  , table'column'labels :: !(Maybe EdhVector)
  } deriving (Typeable)

tableRowCount :: Table -> STM Int
tableRowCount (Table !trcv _ _ _) = readTMVar trcv

tableRowCapacity :: Table -> STM Int
tableRowCapacity (Table _ !cols _ _) = iopdNull cols >>= \case
  True -> return 0
  _ ->
    iopdValues cols
      >>= foldM (\ !cap !col -> min cap <$> columnCapacity col) maxBound

unsafeMarkTableRowCount :: Int -> Table -> STM ()
unsafeMarkTableRowCount !rc (Table !trcv _ _ _) = do
  -- TODO check rc not exceeding cap of any column ?
  void $ tryTakeTMVar trcv
  void $ tryPutTMVar trcv rc

createTable
  :: EdhThreadState
  -> Int
  -> Int
  -> OrderedDict
       AttrKey
       (Int -> TMVar Int -> (Column -> STM ()) -> STM ())
  -> (Table -> STM ())
  -> STM ()
createTable _ets !cap !rowCnt !colCreators !exit = do
  !trcv <- newTMVar rowCnt
  seqcontSTM
      [ \ !exit' -> colCreator cap trcv $ \ !col -> exit' (key, col)
      | (!key, !colCreator) <- odToList colCreators
      ]
    $ \ !colEntries -> iopdFromList colEntries
        >>= \ !tcols -> exit $ Table trcv tcols Nothing Nothing

growTable :: EdhThreadState -> Int -> Table -> STM () -> STM ()
growTable _ets !newRowCnt (Table !trcv !tcols _ _) !exit =
  iopdValues tcols >>= \ !cols -> do
    !trc <- takeTMVar trcv

    sequence_ $ growCol <$> cols

    putTMVar trcv $ min newRowCnt trc

    exit
 where
  growCol :: Column -> STM ()
  growCol (Column (DataType _dti !dtStorable) _ !csv) = do
    !cs  <- readTVar csv
    !cs' <- flat'grow'array dtStorable (coerce cs) newRowCnt
    writeTVar csv (coerce cs')


createTableClass :: Object -> Scope -> STM Object
createTableClass !colClass !clsOuterScope =
  mkHostClass' clsOuterScope "Table" tableAllocator [] $ \ !clsScope -> do
    !mths <-
      sequence
        $ [ (AttrByName nm, ) <$> mkHostProc clsScope vc nm hp mthArgs
          | (nm, vc, hp, mthArgs) <-
            [ ("__cap__", EdhMethod, tabCapProc, PackReceiver [])
            , ( "__grow__"
              , EdhMethod
              , tabGrowProc
              , PackReceiver [mandatoryArg "newCapacity"]
              )
            , ("__len__", EdhMethod, tabLenProc, PackReceiver [])
            , ( "__mark__"
              , EdhMethod
              , tabMarkRowCntProc
              , PackReceiver [mandatoryArg "newRowCount"]
              )
            , ( "[]"
              , EdhMethod
              , tabIdxReadProc
              , PackReceiver [mandatoryArg "idx"]
              )
            , ( "[=]"
              , EdhMethod
              , tabIdxWriteProc
              , PackReceiver [mandatoryArg "idx", mandatoryArg "val"]
              )
            , ( "@"
              , EdhMethod
              , tabAttrReadProc
              , PackReceiver [mandatoryArg "attrKey"]
              )
            , ( "@="
              , EdhMethod
              , tabAttrWriteProc
              , PackReceiver [mandatoryArg "attrKey", mandatoryArg "attrVal"]
              )
            , ("__repr__", EdhMethod, tabReprProc, PackReceiver [])
            , ("__show__", EdhMethod, tabShowProc, PackReceiver [])
            , ("__desc__", EdhMethod, tabDescProc, PackReceiver [])
            ]
          ]
    iopdUpdate mths $ edh'scope'entity clsScope

 where

  -- | host constructor 
  --    Table(
  --       capacity, rowCount, 
  --       col1=<dtype> | <Column>, col2=...
  --    )
  tableAllocator :: EdhObjectAllocator
  tableAllocator !etsCtor (ArgsPack !args !kwargs) !ctorExit =
    parseArgs $ \(!cap, !rowCnt) ->
      odMapContSTM parseColSpec kwargs $ \ !colCreators -> createTable
        etsCtor
        cap
        rowCnt
        colCreators
        ((ctorExit . HostStore =<<) . newTVar . toDyn)
   where
    parseArgs :: ((Int, Int) -> STM ()) -> STM ()
    parseArgs !exit = case args of
      [EdhDecimal !capNum, EdhDecimal !rcNum] -> gotArgs capNum rcNum
      [EdhDecimal !capNum]                    -> gotArgs capNum 0
      _ ->
        throwEdh etsCtor UsageError
          $  "invalid capacity/rowCount to create a Table: "
          <> T.pack (show args)
     where
      gotArgs :: Decimal -> Decimal -> STM ()
      gotArgs !capNum !rcNum = case D.decimalToInteger capNum of
        Just !cap | cap > 0 -> case D.decimalToInteger rcNum of
          Just !rc | rc >= 0 -> exit (fromInteger cap, fromInteger rc)
          _ ->
            throwEdh etsCtor UsageError
              $  "table row count should be zero or a positive integer, not "
              <> T.pack (show rcNum)
        _ ->
          throwEdh etsCtor UsageError
            $  "table capacity should be a positive integer, not "
            <> T.pack (show capNum)

    parseColSpec
      :: EdhValue
      -> ((Int -> TMVar Int -> (Column -> STM ()) -> STM ()) -> STM ())
      -> STM ()
    parseColSpec !val !exit = case edhUltimate val of
      EdhObject !obj -> castObjectStore obj >>= \case
        Just col@Column{} -> exit $ copyCol col
        Nothing           -> castObjectStore obj >>= \case
          Just !dt -> exit $ createCol dt
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

    createCol :: DataType -> Int -> TMVar Int -> (Column -> STM ()) -> STM ()
    createCol !dt !cap !clv !exit = createColumn etsCtor dt cap clv exit

    copyCol :: Column -> Int -> TMVar Int -> (Column -> STM ()) -> STM ()
    copyCol (Column !dti !clvSrc !csvSrc) !cap !clv !exit = do
      !clSrc                  <- readTMVar clvSrc
      (FlatArray _capSrc !fp) <- readTVar csvSrc
      !cs'                    <- unsafeIOToSTM $ do
        !p'  <- callocArray cap
        !fp' <- newForeignPtr finalizerFree p'
        withForeignPtr fp $ \ !p -> copyArray p' p $ min cap clSrc
        return $ FlatArray cap fp'
      !csv' <- newTVar cs'
      exit $ Column dti clv csv'


  tabGrowProc :: EdhHostProc
  tabGrowProc (ArgsPack [EdhDecimal !newCapNum] !kwargs) !exit !ets
    | odNull kwargs = case D.decimalToInteger newCapNum of
      Just !newCap | newCap > 0 -> withThisHostObj ets $ \_hsv !tab ->
        growTable ets (fromInteger newCap) tab
          $ exitEdh ets exit
          $ EdhObject
          $ edh'scope'that
          $ contextScope
          $ edh'context ets
      _ -> throwEdh ets UsageError "table capacity must be a positive integer"
  tabGrowProc _ _ !ets = throwEdh ets UsageError "invalid args to Table.grow()"

  tabCapProc :: EdhHostProc
  tabCapProc _ !exit !ets = withThisHostObj ets $ \_hsv !tab ->
    tableRowCapacity tab
      >>= \ !cap -> exitEdh ets exit $ EdhDecimal $ fromIntegral cap

  tabLenProc :: EdhHostProc
  tabLenProc _ !exit !ets = withThisHostObj ets $ \_hsv !tab ->
    tableRowCount tab
      >>= \ !len -> exitEdh ets exit $ EdhDecimal $ fromIntegral len

  tabMarkRowCntProc :: EdhHostProc
  tabMarkRowCntProc (ArgsPack [EdhDecimal !newLenNum] !kwargs) !exit !ets
    | odNull kwargs = withThisHostObj ets $ \_hsv !tab -> do
      !cap <- tableRowCapacity tab
      case D.decimalToInteger newLenNum of
        Just !newLen | newLen >= 0 && newLen <= fromIntegral cap ->
          unsafeMarkTableRowCount (fromInteger newLen) tab
            >> exitEdh ets exit nil
        _ -> throwEdh ets UsageError "table length out of range"
  tabMarkRowCntProc _ _ !ets =
    throwEdh ets UsageError "invalid args to Table.markLength()"


  tabIdxReadProc :: EdhHostProc
  tabIdxReadProc (ArgsPack [!idxVal] _) !exit !ets =
    -- TODO impl. 
    exitEdh ets exit $ EdhString "<not impl.>"
  tabIdxReadProc !apk _ !ets =
    throwEdh ets EvalError $ "bad args to index a table" <> T.pack (show apk)

  tabIdxWriteProc :: EdhHostProc
  tabIdxWriteProc (ArgsPack [!idxVal, !toVal] _) !exit !ets =
    -- TODO impl. 
    exitEdh ets exit $ EdhString "<not impl.>"
  tabIdxWriteProc !apk _ !ets =
    throwEdh ets EvalError $ "bad args to index assign a table" <> T.pack
      (show apk)


  tabAttrReadProc :: EdhHostProc
  tabAttrReadProc (ArgsPack [!attrKey] _) !exit !ets =
    withThisHostObj ets $ \_hsv (Table _ !tcols _ _) -> case attrKey of
      EdhString !attrName -> iopdLookup (AttrByName attrName) tcols >>= \case
        Nothing -> exitEdh ets exit nil
        Just !col ->
          edhCreateHostObj colClass (toDyn col) []
            >>= exitEdh ets exit
            .   EdhObject
      !badColId ->
        throwEdh ets UsageError $ "invalid Column identifier of " <> T.pack
          (edhTypeNameOf badColId)
  tabAttrReadProc !apk _ !ets =
    throwEdh ets EvalError $ "bad args to get column(s) from a table" <> T.pack
      (show apk)

  tabAttrWriteProc :: EdhHostProc
  tabAttrWriteProc (ArgsPack [!attrKey, !attrVal] _) !exit !ets =
    -- TODO impl. 
    exitEdh ets exit $ EdhString "<not impl.>"
  tabAttrWriteProc !apk _ !ets =
    throwEdh ets EvalError $ "bad args to set column(s) to a table" <> T.pack
      (show apk)


  tabReprProc :: EdhHostProc
  tabReprProc _ !exit !ets =
    withThisHostObj' ets (exitEdh ets exit $ EdhString "<bogus-Table>")
      $ \_hsv tab@(Table !trcv !tcols _ _) -> do
          !trc      <- readTMVar trcv
          !cap      <- tableRowCapacity tab
          !colReprs <-
            (iopdToList tcols >>=) $ (return .) $ fmap $ \(!colKey, !col) ->
              T.pack (show colKey)
                <> "="
                <> data'type'identifier (column'data'type col)
                <> ", "
          exitEdh ets exit
            $  EdhString
            $  "table( "
            <> T.pack (show cap)
            <> ", "
            <> T.pack (show trc)
            <> ", "
            <> T.concat colReprs
            <> ")"


  tabShowProc :: EdhHostProc
  tabShowProc (ArgsPack _ !kwargs) !exit !ets =
    withThisHostObj' ets (exitEdh ets exit $ EdhString "<bogus-Table>")
      $ \_hsv tab@(Table !trcv !tcols _ _) ->
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
  tabDescProc _ !exit !ets =
    withThisHostObj' ets (exitEdh ets exit $ EdhString "<bogus-Table>")
      $ \_hsv tab@(Table !trcv !tcols _ _) -> do
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

