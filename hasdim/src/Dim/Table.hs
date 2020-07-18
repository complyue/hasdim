
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

import           Data.Vector                    ( Vector )
import qualified Data.Vector                   as V

import           Data.Lossless.Decimal         as D

import           Language.Edh.EHI

import           Dim.DataType
import           Dim.Column


data Table = Table {
    -- this is also the mutex to coordinate concurrent modifications to the
    -- table
    table'row'count :: !(TMVar Int)
    -- optional labels associated with each row
  , table'row'labels :: !(Maybe EdhVector)
    -- underlying table storage, represented as columns, those sharing 
  , table'columns :: !(Vector Column)
    -- labels associated with each column, default to their respective index
  , table'column'labels :: !EdhVector
  } deriving (Typeable)

tableRowCount :: Table -> STM Int
tableRowCount (Table !trcv _ _ _) = readTMVar trcv

tableRowCapacity :: Table -> STM Int
tableRowCapacity (Table _ _ !cols _) = if V.length cols < 1
  then return 0
  else V.foldM' (\ !cap !col -> min cap <$> columnCapacity col) maxBound cols

unsafeMarkTableRowCount :: Int -> Table -> STM ()
unsafeMarkTableRowCount !rc (Table !trcv _ _ _) = do
  void $ tryTakeTMVar trcv
  void $ tryPutTMVar trcv rc

createTable
  :: EdhProgState
  -> Int
  -> Int
  -> [(EdhValue, Int -> TMVar Int -> (Column -> STM ()) -> STM ())]
  -> (Table -> STM ())
  -> STM ()
createTable _pgs !cap !rowCnt !colCreators !exit = do
  !trcv      <- newTMVar rowCnt
  !colLabels <- unsafeIOToSTM $ V.unsafeThaw $ V.fromList
    [ label | (label, _dti) <- colCreators ]
  seqcontSTM [ colCreator cap trcv | (_label, colCreator) <- colCreators ]
    $ \ !cols -> exit $ Table trcv Nothing (V.fromList cols) colLabels

growTable :: EdhProgState -> Int -> Table -> STM () -> STM ()
growTable !pgs !newRowCnt (Table !trcv _ !cols _) !exit =
  seqcontSTM [ resolveDataType pgs dti | (Column !dti _ _) <- V.toList cols ]
    $ \ !dtl -> flip (edhPerformSTM pgs) (const $ contEdhSTM exit) $ do
        !trc <- takeTMVar trcv

        forM_ [ (dt, col) | (dt, col) <- zip dtl (V.toList cols) ]
          $ uncurry growCol

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
  parseArgs $ \(cap, rowCnt) -> seqcontSTM (parseColSpec <$> odToList kwargs)
    $ \ !specs -> createTable pgsCtor cap rowCnt specs (ctorExit . toDyn)
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
    :: (AttrKey, EdhValue)
    -> (  (EdhValue, Int -> TMVar Int -> (Column -> STM ()) -> STM ())
       -> STM ()
       )
    -> STM ()
  parseColSpec (!key, !val) !exit = case edhUltimate val of
    EdhString !dti -> exit (attrKeyValue key, createCol dti)
    EdhObject !obj -> castObjectStore obj >>= \case
      Just col@Column{} -> exit (attrKeyValue key, copyCol col)
      Nothing ->
        throwEdhSTM pgsCtor UsageError $ "Not a Column object for " <> T.pack
          (show key)
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


tabMethods :: EdhProgState -> STM [(AttrKey, EdhValue)]
tabMethods !pgsModule =
  sequence
    $  [ (AttrByName nm, ) <$> mkHostProc scope vc nm hp mthArgs
       | (nm, vc, hp, mthArgs) <-
         [ ( "grow"
           , EdhMethod
           , tabGrowProc
           , PackReceiver [mandatoryArg "newCapacity"]
           )
--  , ("[]", EdhMethod, tabIdxReadProc, PackReceiver [mandatoryArg "idx"])
--  , ( "[=]"
--    , EdhMethod
--    , tabIdxWriteProc
--    , PackReceiver [mandatoryArg "idx", mandatoryArg "val"]
--    )
         , ("@"       , EdhMethod, tabAttrProc, PackReceiver [])
         , ("__repr__", EdhMethod, tabReprProc, PackReceiver [])
--  , ("__show__", EdhMethod, tabShowProc, PackReceiver [])
--  , ("__desc__", EdhMethod, tabDescProc, PackReceiver [])
         ]
       ]
    ++ [ (AttrByName nm, ) <$> mkHostProperty scope nm getter setter
       | (nm, getter, setter) <-
         [ ("capacity", tabCapProc, Nothing)
         , ("length"  , tabLenProc, Just tabMarkLenProc)
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

  tabMarkLenProc :: EdhProcedure
  tabMarkLenProc (ArgsPack [EdhDecimal !newLenNum] !kwargs) !exit
    | odNull kwargs = withThatEntity $ \ !pgs !tab -> do
      !cap <- tableRowCapacity tab
      case D.decimalToInteger newLenNum of
        Just !newLen | newLen >= 0 && newLen <= fromIntegral cap ->
          unsafeMarkTableRowCount (fromInteger newLen) tab
            >> exitEdhSTM pgs exit nil
        _ -> throwEdhSTM pgs UsageError "Table length out of range"
  tabMarkLenProc _ _ = throwEdh UsageError "Invalid args to Table.markLength()"

  tabAttrProc :: EdhProcedure
  tabAttrProc (ArgsPack [!attrKey] _) !exit =
    -- TODO impl. 
    exitEdhProc exit $ EdhString "<not impl.>"
  tabAttrProc _ _ = throwEdh EvalError "bug: unexpected args to (@)"

  tabReprProc :: EdhProcedure
  tabReprProc _ !exit =
    withThatEntity' (\ !pgs -> exitEdhSTM pgs exit $ EdhString "<bogus-Table>")
      $ \ !pgs tab@(Table !trcv _rowLabels !_cols !_colLabels) -> do
          !rc  <- readTMVar trcv
          !cap <- tableRowCapacity tab
          exitEdhSTM pgs exit
            $  EdhString
            $  "Table("
            <> T.pack (show cap)
            <> ", "
            <> T.pack (show rc)
          -- TODO fill here with column identifier and their dtypes
            <> ", ...)"

