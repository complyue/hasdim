
module Dim.DataType where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Foreign

import           Control.Monad.Reader

import           Control.Concurrent.STM


import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.HashMap.Strict           as Map
import           Data.Dynamic


-- import           Data.Vector.Storable          as V
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
  reguIdx !pgs !vec !idx !exit =
    let !posIdx = if idx < 0  -- Python style negative index
          then idx + MV.length vec
          else idx
    in  if posIdx < 0 || posIdx >= MV.length vec
          then
            throwEdhSTM pgs EvalError
            $  "Index out of bounds: "
            <> T.pack (show idx)
            <> " vs "
            <> T.pack (show $ MV.length vec)
          else exit posIdx
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
  readVectorCell !pgs !idx !vec !exit = reguIdx pgs vec idx $ \ !posIdx ->
    edhPerformIO pgs (MV.unsafeWith vec $ \ !vPtr -> peekElemOff vPtr posIdx)
      $ \ !sv -> contEdhSTM $ toEdh pgs sv $ \ !val -> exit val
  writeVectorCell !pgs !val !idx !vec !exit =
    reguIdx pgs vec idx $ \ !posIdx -> fromEdh pgs val $ \ !sv -> do
      unsafeIOToSTM $ MV.unsafeWith vec $ \ !vPtr -> pokeElemOff vPtr posIdx sv
      toEdh pgs sv $ \ !val' -> exit val'
  updateVector _ [] _ !exit = exit
  updateVector !pgs ((!idx, !sv) : rest'upds) !vec !exit =
    reguIdx pgs vec idx $ \ !posIdx -> do
      unsafeIOToSTM $ MV.unsafeWith vec $ \ !vPtr -> pokeElemOff vPtr posIdx sv
      updateVector pgs rest'upds vec exit


data ConcreteDataType where
  ConcreteDataType ::(Storable a, EdhXchg a) => {
      concrete'data'type'repr :: !Text
    , concrete'data'type :: !(DataType a)
    } -> ConcreteDataType
 deriving Typeable

-- | host Class dtype()
dtypeCtor
  :: EdhProgState
  -> ArgsPack  -- ctor args, if __init__() is provided, will go there too
  -> TVar (Map.HashMap AttrKey EdhValue)  -- out-of-band attr store
  -> (Dynamic -> STM ())  -- in-band data to be written to entity store
  -> STM ()
dtypeCtor !pgsCtor _ !obs !ctorExit = do
  let !scope = contextScope $ edh'context pgsCtor
  methods <- sequence
    [ (AttrByName nm, ) <$> mkHostProc scope vc nm hp args
    | (nm, vc, hp, args) <-
      [("__repr__", EdhMethod, dtypeReprProc, PackReceiver [])]
    ]
  modifyTVar' obs $ Map.union $ Map.fromList methods
  ctorExit $ toDyn nil
 where
  dtypeReprProc :: EdhProcedure
  dtypeReprProc _ !exit = do
    pgs <- ask
    let ctx  = edh'context pgs
        this = thisObject $ contextScope ctx
        es   = entity'store $ objEntity this
    contEdhSTM $ do
      esd <- readTVar es
      case fromDynamic esd :: Maybe ConcreteDataType of
        Just (ConcreteDataType !repr _) -> exitEdhSTM pgs exit $ EdhString repr
        _ -> exitEdhSTM pgs exit $ EdhString "<Not-a-DataType>"

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
