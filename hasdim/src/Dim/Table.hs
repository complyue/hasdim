
module Dim.Table where

import           Prelude
-- import           Debug.Trace

-- import           Unsafe.Coerce
import           GHC.Conc                       ( unsafeIOToSTM )

-- import           Foreign                 hiding ( void )

import           Control.Monad
-- import           Control.Monad.Reader

import           Control.Concurrent.STM

-- import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.HashMap.Strict           as Map

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
  -> [(EdhValue, DataTypeIdent)]
  -> (Table -> STM ())
  -> STM ()
createTable !pgs !cap !col2dtype !exit = do
  !trcv      <- newTMVar 0
  !colLabels <- unsafeIOToSTM $ V.unsafeThaw $ V.fromList
    [ label | (label, _dti) <- col2dtype ]
  seqcontSTM [ createColumn pgs dti cap trcv | (_label, dti) <- col2dtype ]
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


-- | host constructor Table(capacity, *columns=(col1:dtype1, ...))
tabCtor :: EdhHostCtor
tabCtor !pgsCtor (ArgsPack ((EdhDecimal !capNum) : columnSpecs) _kwargs) !ctorExit
  = case D.decimalToInteger capNum of
    Just !cap | cap > 0 ->
      seqcontSTM (parseColSpec <$> columnSpecs) $ \ !specs ->
        createTable pgsCtor (fromInteger cap) specs (ctorExit . toDyn)
    _ ->
      throwEdhSTM pgsCtor UsageError
        $  "Table capacity should be a positive integer, not "
        <> T.pack (show capNum)
 where
  parseColSpec :: EdhValue -> ((EdhValue, DataTypeIdent) -> STM ()) -> STM ()
  parseColSpec !val !exit = case val of
    EdhPair !colIdent !colDtype -> case edhUltimate colDtype of
      EdhString !dti -> exit (colIdent, dti)
      !badDti        -> edhValueReprSTM pgsCtor badDti $ \ !dtiRepr ->
        throwEdhSTM pgsCtor UsageError $ "Invalid dtype identifier: " <> dtiRepr
    !badColSpec -> edhValueReprSTM pgsCtor badColSpec $ \ !specRepr ->
      throwEdhSTM pgsCtor UsageError
        $  "Invalid column specification: "
        <> specRepr
tabCtor !pgsCtor !apk _ =
  throwEdhSTM pgsCtor UsageError
    $  "Invalid args for Table construction: "
    <> T.pack (show apk)

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
  tabGrowProc (ArgsPack [EdhDecimal !newCapNum] !kwargs) !exit
    | Map.null kwargs = case D.decimalToInteger newCapNum of
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
    | Map.null kwargs = withThatEntity $ \ !pgs !tab -> do
      !cap <- tableRowCapacity tab
      case D.decimalToInteger newLenNum of
        Just !newLen | newLen >= 0 && newLen <= fromIntegral cap ->
          unsafeMarkTableRowCount (fromInteger newLen) tab
            >> exitEdhSTM pgs exit nil
        _ -> throwEdhSTM pgs UsageError "Table length out of range"
  tabMarkLenProc _ _ = throwEdh UsageError "Invalid args to Table.markLength()"

  tabReprProc :: EdhProcedure
  tabReprProc _ !exit =
    withThatEntity' (\ !pgs -> exitEdhSTM pgs exit $ EdhString "<bogus-Table>")
      $ \ !pgs tab@(Table _trcv _rowLabels !_cols !_colLabels) -> do
          !cap <- tableRowCapacity tab
          -- TODO impl. this
          exitEdhSTM pgs exit
            $  EdhString
            $  "Table("
            <> T.pack (show cap)
            <> ", ...)"

