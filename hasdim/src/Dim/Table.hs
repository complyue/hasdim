
module Dim.Table where

import           Prelude
-- import           Debug.Trace

-- import           Unsafe.Coerce
import           GHC.Conc                       ( unsafeIOToSTM )

import           Foreign                 hiding ( void )

import           Control.Monad
-- import           Control.Monad.Reader

import           Control.Concurrent.STM

-- import           Data.Text                      ( Text )
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
  :: EdhProgState
  -> Int
  -> Int
  -> OrderedDict
       AttrKey
       (Int -> TMVar Int -> (Column -> STM ()) -> STM ())
  -> (Table -> STM ())
  -> STM ()
createTable _pgs !cap !rowCnt !colCreators !exit = do
  !trcv <- newTMVar rowCnt
  seqcontSTM
      [ \ !exit' -> colCreator cap trcv $ \ !col -> exit' (key, col)
      | (!key, !colCreator) <- odToList colCreators
      ]
    $ \ !colEntries -> iopdFromList colEntries
        >>= \ !tcols -> exit $ Table trcv tcols Nothing Nothing

growTable :: EdhProgState -> Int -> Table -> STM () -> STM ()
growTable !pgs !newRowCnt (Table !trcv !tcols _ _) !exit =
  iopdValues tcols >>= \ !cols ->
    seqcontSTM [ resolveDataType pgs dti | (Column !dti _ _) <- cols ]
      $ \ !dtl -> flip (edhPerformSTM pgs) (const $ contEdhSTM exit) $ do
          !trc <- takeTMVar trcv

          forM_ [ (dt, col) | (dt, col) <- zip dtl cols ] $ uncurry growCol

          putTMVar trcv $ min newRowCnt trc
 where
  growCol :: DataType -> Column -> STM ()
  growCol (DataType _dti !dtStorable) (Column _ _ !csv) = do
    !cs  <- readTVar csv
    !cs' <- flat'grow'array dtStorable (coerce cs) newRowCnt
    writeTVar csv (coerce cs')


-- | host constructor Table( capacity, rowCount, col1=<dtype> | <Column>, col2=... )
tabCtor :: EdhHostCtor
tabCtor !pgsCtor (ArgsPack !args !kwargs) !ctorExit =
  parseArgs $ \(!cap, !rowCnt) ->
    odMapContSTM parseColSpec kwargs $ \ !colCreators ->
      createTable pgsCtor cap rowCnt colCreators $ ctorExit . toDyn
 where
  parseArgs :: ((Int, Int) -> STM ()) -> STM ()
  parseArgs !exit = case args of
    [EdhDecimal !capNum, EdhDecimal !rcNum] -> gotArgs capNum rcNum
    [EdhDecimal !capNum]                    -> gotArgs capNum 0
    _ ->
      throwEdhSTM pgsCtor UsageError
        $  "Invalid capacity/rowCount to create a Table: "
        <> T.pack (show args)
   where
    gotArgs :: Decimal -> Decimal -> STM ()
    gotArgs !capNum !rcNum = case D.decimalToInteger capNum of
      Just !cap | cap > 0 -> case D.decimalToInteger rcNum of
        Just !rc | rc >= 0 -> exit (fromInteger cap, fromInteger rc)
        _ ->
          throwEdhSTM pgsCtor UsageError
            $  "Table row count should be zero or a positive integer, not "
            <> T.pack (show rcNum)
      _ ->
        throwEdhSTM pgsCtor UsageError
          $  "Table capacity should be a positive integer, not "
          <> T.pack (show capNum)

  parseColSpec
    :: EdhValue
    -> ((Int -> TMVar Int -> (Column -> STM ()) -> STM ()) -> STM ())
    -> STM ()
  parseColSpec !val !exit = case edhUltimate val of
    EdhString !dti -> exit $ createCol dti
    EdhObject !obj -> castObjectStore obj >>= \case
      Just col@Column{} -> exit $ copyCol col
      Nothing -> throwEdhSTM pgsCtor UsageError $ "Not a Column object"
    !badColSpec -> edhValueReprSTM pgsCtor badColSpec $ \ !colRepr ->
      throwEdhSTM pgsCtor UsageError
        $  "Invalid column specification, "
        <> T.pack (show $ edhTypeNameOf badColSpec)
        <> ": "
        <> colRepr

  createCol :: DataTypeIdent -> Int -> TMVar Int -> (Column -> STM ()) -> STM ()
  createCol !dti !cap !clv !exit = createColumn pgsCtor dti cap clv exit

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


tabMethods :: Object -> EdhProgState -> STM [(AttrKey, EdhValue)]
tabMethods !colt !pgsModule =
  sequence
    $ [ (AttrByName nm, ) <$> mkHostProc scope vc nm hp mthArgs
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
        , ("[]", EdhMethod, tabIdxReadProc, PackReceiver [mandatoryArg "idx"])
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
 where
  !scope = contextScope $ edh'context pgsModule

  tabGrowProc :: EdhProcedure
  tabGrowProc (ArgsPack [EdhDecimal !newCapNum] !kwargs) !exit | odNull kwargs =
    case D.decimalToInteger newCapNum of
      Just !newCap | newCap > 0 -> withThatEntity $ \ !pgs !tab ->
        growTable pgs (fromInteger newCap) tab
          $ exitEdhSTM pgs exit
          $ EdhObject
          $ thatObject
          $ contextScope
          $ edh'context pgs
      _ -> throwEdh UsageError "Table capacity must be a positive integer"
  tabGrowProc _ _ = throwEdh UsageError "Invalid args to Table.grow()"

  tabCapProc :: EdhProcedure
  tabCapProc _ !exit = withThatEntity $ \ !pgs !tab -> tableRowCapacity tab
    >>= \ !cap -> exitEdhSTM pgs exit $ EdhDecimal $ fromIntegral cap

  tabLenProc :: EdhProcedure
  tabLenProc _ !exit = withThatEntity $ \ !pgs !tab -> tableRowCount tab
    >>= \ !len -> exitEdhSTM pgs exit $ EdhDecimal $ fromIntegral len

  tabMarkRowCntProc :: EdhProcedure
  tabMarkRowCntProc (ArgsPack [EdhDecimal !newLenNum] !kwargs) !exit
    | odNull kwargs = withThatEntity $ \ !pgs !tab -> do
      !cap <- tableRowCapacity tab
      case D.decimalToInteger newLenNum of
        Just !newLen | newLen >= 0 && newLen <= fromIntegral cap ->
          unsafeMarkTableRowCount (fromInteger newLen) tab
            >> exitEdhSTM pgs exit nil
        _ -> throwEdhSTM pgs UsageError "Table length out of range"
  tabMarkRowCntProc _ _ =
    throwEdh UsageError "Invalid args to Table.markLength()"


  tabIdxReadProc :: EdhProcedure
  tabIdxReadProc (ArgsPack [!idxVal] _) !exit =
    -- TODO impl. 
    exitEdhProc exit $ EdhString "<not impl.>"
  tabIdxReadProc !apk _ =
    throwEdh EvalError $ "Bad args to index a table" <> T.pack (show apk)

  tabIdxWriteProc :: EdhProcedure
  tabIdxWriteProc (ArgsPack [!idxVal, !toVal] _) !exit =
    -- TODO impl. 
    exitEdhProc exit $ EdhString "<not impl.>"
  tabIdxWriteProc !apk _ =
    throwEdh EvalError $ "Bad args to index assign a table" <> T.pack (show apk)


  tabAttrReadProc :: EdhProcedure
  tabAttrReadProc (ArgsPack [!attrKey] _) !exit =
    withThatEntity $ \ !pgs (Table _ !tcols _ _) -> case attrKey of
      EdhString !attrName -> iopdLookup (AttrByName attrName) tcols >>= \case
        Nothing   -> exitEdhSTM pgs exit nil
        Just !col -> cloneEdhObject colt (\_ !cloneTo -> cloneTo $ toDyn col)
          $ \ !colObj -> exitEdhSTM pgs exit $ EdhObject colObj
      !badColId ->
        throwEdhSTM pgs UsageError $ "Invalid Column identifier of " <> T.pack
          (edhTypeNameOf badColId)
  tabAttrReadProc !apk _ =
    throwEdh EvalError $ "Bad args to get column(s) from a table" <> T.pack
      (show apk)

  tabAttrWriteProc :: EdhProcedure
  tabAttrWriteProc (ArgsPack [!attrKey, !attrVal] _) !exit =
    -- TODO impl. 
    exitEdhProc exit $ EdhString "<not impl.>"
  tabAttrWriteProc !apk _ =
    throwEdh EvalError $ "Bad args to set column(s) to a table" <> T.pack
      (show apk)


  tabReprProc :: EdhProcedure
  tabReprProc _ !exit =
    withThatEntity' (\ !pgs -> exitEdhSTM pgs exit $ EdhString "<bogus-Table>")
      $ \ !pgs tab@(Table !trcv !tcols _ _) -> do
          !trc      <- readTMVar trcv
          !cap      <- tableRowCapacity tab
          !colReprs <-
            (iopdToList tcols >>=) $ (return .) $ fmap $ \(!colKey, !col) ->
              T.pack (show colKey) <> "=" <> column'data'type col <> ", "
          exitEdhSTM pgs exit
            $  EdhString
            $  "Table( "
            <> T.pack (show cap)
            <> ", "
            <> T.pack (show trc)
            <> ", "
            <> T.concat colReprs
            <> ")"

  tabShowProc :: EdhProcedure
  tabShowProc _ !exit =
    withThatEntity' (\ !pgs -> exitEdhSTM pgs exit $ EdhString "<bogus-Table>")
      $ \ !pgs tab@(Table !trcv !tcols _ _) -> do
          !trc <- readTMVar trcv
          exitEdhSTM pgs exit
            $  EdhString
            $  "Table:\n * Row Count: "
            <> T.pack (show trc)
          -- TODO fill here with column data
            <> "...\n"

  tabDescProc :: EdhProcedure
  tabDescProc _ !exit =
    withThatEntity' (\ !pgs -> exitEdhSTM pgs exit $ EdhString "<bogus-Table>")
      $ \ !pgs tab@(Table !trcv !tcols _ _) -> do
          !trc <- readTMVar trcv
          exitEdhSTM pgs exit
            $  EdhString
            $  "Table:\n * Row Count: "
            <> T.pack (show trc)
          -- TODO fill here with column statistics
            <> "...\n"

