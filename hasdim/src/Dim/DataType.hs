
module Dim.DataType where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Foreign

import           Control.Monad.Reader

import           Control.Concurrent.STM


import           Data.Text                      ( Text )
import           Data.Dynamic

import           Data.Vector.Storable.Mutable  as MV

import           Language.Edh.EHI

import           Dim.XCHG


-- type safe data manipulation operations wrt to exchanging data with Edh
-- programs
data DataType a where
  DataType ::(Storable a, EdhXchg a) => {
      create'data'vector :: EdhProgState
        ->  Int -> (IOVector a -> STM ()) -> STM ()
    , grow'data'vector :: EdhProgState
        -> IOVector a -> Int -> (IOVector a -> STM ()) -> STM ()
    , read'data'vector'cell :: EdhProgState
        -> Int -> IOVector a -> (EdhValue -> STM ()) -> STM ()
    , write'data'vector'cell :: EdhProgState
        -> EdhValue -> Int -> IOVector a -> (EdhValue -> STM ()) -> STM ()
    , update'data'vector :: EdhProgState
        -> [(Int,a)]  -> IOVector a  -> STM () -> STM ()
  }-> DataType a
 deriving Typeable
dataType :: forall a . (Storable a, EdhXchg a) => DataType a
dataType = DataType createVector
                    growVector
                    readVectorCell
                    writeVectorCell
                    updateVector
 where
  createVector !_ !cap !exit = do
    vec <- unsafeIOToSTM $ do
      !p  <- callocArray cap
      !fp <- newForeignPtr finalizerFree p
      return $ MV.unsafeFromForeignPtr0 fp cap
    exit vec
  growVector _ !vec !cap !exit = if cap <= MV.length vec
    then exit $ MV.unsafeSlice 0 cap vec
    else do
      vec' <- unsafeIOToSTM $ do
        !p'  <- callocArray cap
        !fp' <- newForeignPtr finalizerFree p'
        MV.unsafeWith vec $ \ !p -> copyArray p' p $ MV.length vec
        return $ MV.unsafeFromForeignPtr0 fp' cap
      exit vec'
  readVectorCell !pgs !idx !vec !exit =
    edhRegulateIndex pgs (MV.length vec) idx $ \ !posIdx ->
      edhPerformIO pgs (MV.unsafeWith vec $ \ !vPtr -> peekElemOff vPtr posIdx)
        $ \ !sv -> contEdhSTM $ toEdh pgs sv $ \ !val -> exit val
  writeVectorCell !pgs !val !idx !vec !exit =
    edhRegulateIndex pgs (MV.length vec) idx $ \ !posIdx ->
      fromEdh pgs val $ \ !sv -> do
        unsafeIOToSTM $ MV.unsafeWith vec $ \ !vPtr ->
          pokeElemOff vPtr posIdx sv
        toEdh pgs sv $ \ !val' -> exit val'
  updateVector _ [] _ !exit = exit
  updateVector !pgs ((!idx, !sv) : rest'upds) !vec !exit =
    edhRegulateIndex pgs (MV.length vec) idx $ \ !posIdx -> do
      unsafeIOToSTM $ MV.unsafeWith vec $ \ !vPtr -> pokeElemOff vPtr posIdx sv
      updateVector pgs rest'upds vec exit


data ConcreteDataType where
  ConcreteDataType ::(Storable a, EdhXchg a) => {
      concrete'data'type'repr :: !Text
    , concrete'data'type :: !(DataType a)
    } -> ConcreteDataType
 deriving Typeable

-- | host Class dtype()
dtypeCtor :: EdhHostCtor
-- not really constructable from Edh code, relies on host code to fill
-- the in-band storage
dtypeCtor _ _ !ctorExit = ctorExit $ toDyn nil

dtypeMethods :: EdhProgState -> STM [(AttrKey, EdhValue)]
dtypeMethods !pgsModule = sequence
  [ (AttrByName nm, ) <$> mkHostProc scope vc nm hp args
  | (nm, vc, hp, args) <-
    [ ("__init__", EdhMethod, dtypeInitProc, PackReceiver [mandatoryArg "name"])
    , ("=="      , EdhMethod, dtypeEqProc  , PackReceiver [])
    , ("__repr__", EdhMethod, dtypeReprProc, PackReceiver [])
    ]
  ]
 where
  !scope = contextScope $ edh'context pgsModule

  dtypeInitProc :: EdhProcedure
  dtypeInitProc (ArgsPack !args _) !exit = case args of
    [EdhString !name] -> ask >>= \ !pgs -> do
      let !dtCls = objClass $ thisObject $ contextScope $ edh'context pgs
      case procedure'lexi dtCls of
        Nothing -> exitEdhProc exit nil
        Just !clsLexi ->
          contEdhSTM $ lookupEdhCtxAttr pgs clsLexi (AttrByName name) >>= \case
            EdhNil -> throwEdhSTM pgs EvalError $ "No such dtype: " <> name
            dtv@(EdhObject !dto) ->
              fromDynamic <$> readTVar (entity'store $ objEntity dto) >>= \case
                Nothing                 -> exitEdhSTM pgs exit nil
                Just ConcreteDataType{} -> exitEdhSTM pgs exit dtv
            _ -> exitEdhSTM pgs exit nil
    _ -> throwEdh UsageError "Invalid args to dtype()"

  dtypeEqProc :: EdhProcedure
  dtypeEqProc (ArgsPack [EdhObject !dtoOther] _) !exit =
    withThatEntityStore $ \ !pgs (ConcreteDataType !repr _) ->
      fromDynamic <$> readTVar (entity'store $ objEntity dtoOther) >>= \case
        Nothing -> exitEdhSTM pgs exit $ EdhBool False
        Just (ConcreteDataType !reprOther _) ->
          exitEdhSTM pgs exit $ EdhBool $ reprOther == repr
  dtypeEqProc _ !exit = exitEdhProc exit $ EdhBool False

  dtypeReprProc :: EdhProcedure
  dtypeReprProc _ !exit =
    withThatEntityStore'
        (\ !pgs -> exitEdhSTM pgs exit $ EdhString "<bad-dtype>")
      $ \ !pgs (ConcreteDataType !repr _) ->
          exitEdhSTM pgs exit $ EdhString repr

wrapDataType
  :: EdhProgState
  -> ProcDefi
  -> (ConcreteDataType, [Text])
  -> (([Text], EdhValue) -> STM ())
  -> STM ()
wrapDataType !pgs !dtypeClass (dt@(ConcreteDataType !repr _), !alias) !exit' =
  runEdhProc pgs
    $ createEdhObject dtypeClass (ArgsPack [] mempty)
    $ \(OriginalValue !dtypeVal _ _) -> case dtypeVal of
        EdhObject !dtObj -> contEdhSTM $ do
          -- actually fill in the in-band entity storage here
          writeTVar (entity'store $ objEntity dtObj) $ toDyn dt
          exit' (repr : alias, dtypeVal)
        _ -> error "bug: dtypeCtor returned non-object"
