module Dim.ColArts where

-- import           Debug.Trace

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import qualified Data.ByteString.Internal as B
import Data.Dynamic
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as T
import Data.Unique
import qualified Data.Vector.Mutable as MV
import Dim.Column
import Dim.FlatArray
import Dim.InMem
import Event.Analytics.EHI
import Foreign hiding (void)
import Language.Edh.EHI
import System.Random
import Type.Reflection
import Prelude

createColumnClass :: Object -> Edh Object
createColumnClass !defaultDt =
  mkEdhClass "Column" (allocObjM columnAllocator) [] $ do
    !mths <-
      sequence $
        [ (AttrByName nm,) <$> mkEdhProc vc nm hp
          | (nm, vc, hp) <-
              [ ("__init__", EdhMethod, wrapEdhProc col__init__),
                ("__cap__", EdhMethod, wrapEdhProc colCapProc),
                ("__len__", EdhMethod, wrapEdhProc colLenProc),
                ("__grow__", EdhMethod, wrapEdhProc colGrowProc),
                ("__mark__", EdhMethod, wrapEdhProc colMarkLenProc),
                ("__blob__", EdhMethod, wrapEdhProc colBlobProc),
                ("__json__", EdhMethod, wrapEdhProc colJsonProc),
                ("__repr__", EdhMethod, wrapEdhProc colReprProc),
                ("__show__", EdhMethod, wrapEdhProc colShowProc),
                ("__desc__", EdhMethod, wrapEdhProc colDescProc),
                ("([])", EdhMethod, wrapEdhProc colIdxReadProc),
                ("([=])", EdhMethod, wrapEdhProc colIdxWriteProc),
                {- -- TODO impl. following by super dtypes
                ("([++=])", EdhMethod, wrapEdhProc $ colIdxUpdWithOpProc "++"),
                ("([+=])", EdhMethod, wrapEdhProc $ colIdxUpdWithOpProc "+"),
                ("([-=])", EdhMethod, wrapEdhProc $ colIdxUpdWithOpProc "-"),
                ("([*=])", EdhMethod, wrapEdhProc $ colIdxUpdWithOpProc "*"),
                ("([/=])", EdhMethod, wrapEdhProc $ colIdxUpdWithOpProc "/"),
                ("([//=])", EdhMethod, wrapEdhProc $ colIdxUpdWithOpProc "//"),
                ("([**=])", EdhMethod, wrapEdhProc $ colIdxUpdWithOpProc "**"),
                ("([&&=])", EdhMethod, wrapEdhProc $ colIdxUpdWithOpProc "&&"),
                ("([||=])", EdhMethod, wrapEdhProc $ colIdxUpdWithOpProc "||"),
                -}
                ("copy", EdhMethod, wrapEdhProc colCopyProc)
              ]
        ]
          ++ [ (AttrByName nm,) <$> mkEdhProperty nm getter setter
               | (nm, getter, setter) <- [("dtype", colDtypeProc, Nothing)]
             ]
    !clsScope <- contextScope . edh'context <$> edhThreadState
    iopdUpdateEdh mths $ edh'scope'entity clsScope
  where
    columnAllocator ::
      "capacity" !: Int ->
      "length" ?: Int ->
      "dtype" ?: Object ->
      ArgsPack -> -- allow/ignore arbitrary ctor args for descendant classes
      Edh (Maybe Unique, ObjectStore)
    columnAllocator
      (mandatoryArg -> !ctorCap)
      (defaultArg ctorCap -> !ctorLen)
      (defaultArg defaultDt -> dto)
      _ctorOtherArgs
        | ctorCap < 0 =
          throwEdhM UsageError $
            "Column capacity can not be negative: " <> T.pack (show ctorCap)
        | ctorLen < 0 =
          throwEdhM UsageError $
            "Column length can not be negative: " <> T.pack (show ctorLen)
        | ctorLen > ctorCap =
          throwEdhM UsageError $
            "Column length can not be larger than capacity: "
              <> T.pack (show ctorLen)
              <> " vs "
              <> T.pack (show ctorCap)
        | otherwise = withDataType dto $ \case
          DeviceDt (_dt :: DeviceDataType a) -> do
            (_fp, !cs) <- liftIO $ newDeviceArray @a ctorCap
            !csv <- newTMVarEdh cs
            !clv <- newTVarEdh ctorLen
            return
              ( Nothing,
                HostStore $
                  toDyn $
                    SomeColumn (typeRep @DeviceArray) $
                      InMemDevCol @a csv clv
              )
          DirectDt dt -> case direct'data'default dt of
            (fill'val :: a) -> do
              (_iov, !cs) <- liftIO $ newDirectArray' @a fill'val ctorCap
              !csv <- newTMVarEdh cs
              !clv <- newTVarEdh ctorLen
              return
                ( Nothing,
                  HostStore $
                    toDyn $
                      SomeColumn (typeRep @DirectArray) $
                        InMemDirCol @a csv clv
                )
          DummyDt dti ->
            naM $ "you don't create Column of dummy dtype: " <> dti

    col__init__ ::
      "capacity" !: Int ->
      "length" ?: Int ->
      "dtype" ?: Object ->
      ArgsPack -> -- allow/ignore arbitrary ctor args for descendant classes
      Edh EdhValue
    col__init__
      _cap
      _len
      (defaultArg defaultDt -> dto)
      _ctorOtherArgs = do
        ets <- edhThreadState
        let scope = contextScope $ edh'context ets
            this = edh'scope'this scope
            that = edh'scope'that scope

            extendsDt :: [Object] -> Edh ()
            extendsDt [] = return ()
            extendsDt (o : rest) = do
              modifyTVarEdh' (edh'obj'supers o) (++ [dto])
              if o == this
                then return ()
                else extendsDt rest

        supers <- readTVarEdh $ edh'obj'supers that
        extendsDt $ that : supers
        return nil

    withThisColumn :: forall r. (Object -> SomeColumn -> Edh r) -> Edh r
    withThisColumn withCol = do
      !this <- edh'scope'this . contextScope . edh'context <$> edhThreadState
      case fromDynamic =<< dynamicHostData this of
        Nothing -> throwEdhM EvalError "bug: this is not a Column"
        Just !col -> withCol this col

    colCapProc :: Edh EdhValue
    colCapProc =
      withThisColumn $ \_this (SomeColumn _ !col) ->
        liftEIO (view'column'data col) >>= \(cs, _cl) ->
          return $ EdhDecimal $ fromIntegral $ array'capacity cs

    colLenProc :: Edh EdhValue
    colLenProc =
      withThisColumn $ \_this (SomeColumn _ !col) ->
        liftEIO (read'column'length col) >>= \ !len ->
          return $ EdhDecimal $ fromIntegral len

    colGrowProc :: "newCap" !: Int -> Edh EdhValue
    colGrowProc (mandatoryArg -> !newCap) =
      if newCap < 0
        then
          throwEdhM UsageError $
            "invalid newCap: " <> T.pack (show newCap)
        else withThisColumn $ \_this (SomeColumn _ !col) -> do
          void $ liftEIO $ grow'column'capacity col newCap
          EdhObject . edh'scope'that . contextScope . edh'context
            <$> edhThreadState

    colMarkLenProc :: "newLen" !: Int -> Edh EdhValue
    colMarkLenProc (mandatoryArg -> !newLen) = withThisColumn $
      \_this (SomeColumn _ !col) -> do
        void $ liftEIO $ mark'column'length col newLen
        EdhObject . edh'scope'that . contextScope . edh'context
          <$> edhThreadState

    colBlobProc :: Edh EdhValue
    colBlobProc = withThisColumn $ \_this (SomeColumn _ !col) -> do
      (cs, cl) <- liftEIO $ view'column'data col
      (<|> return edhNA) $
        array'data'ptr cs $ \(fp :: ForeignPtr a) ->
          return $
            EdhBlob $
              B.fromForeignPtr
                (castForeignPtr fp)
                0
                (cl * sizeOf (undefined :: a))

    colJsonProc :: Edh EdhValue
    colJsonProc = withThisColumn $ \_this (SomeColumn _ !col) -> do
      (cs, cl) <- liftEIO $ view'column'data col
      if cl < 1
        then return $ EdhString "[]"
        else do
          let go :: Int -> [Text] -> Edh EdhValue
              go !i !elemJsonStrs
                | i < 0 =
                  return $
                    EdhString $
                      "[" <> T.intercalate "," elemJsonStrs <> "]"
                | otherwise = do
                  !ev <- liftIO $ array'reader cs i
                  !elemVal <- toEdh ev
                  !elemJsonStr <- edhValueJsonM elemVal
                  go (i -1) $ elemJsonStr : elemJsonStrs
          go (cl - 1) []

    colReprProc :: Edh EdhValue
    colReprProc = withThisColumn $ \this (SomeColumn _ !col) -> do
      (cs, cl) <- liftEIO $ view'column'data col
      !dto <- getColumnDtype this
      !dtRepr <- edhObjReprM dto
      let colRepr =
            "Column( capacity= "
              <> T.pack (show $ array'capacity cs)
              <> ", length= "
              <> T.pack (show cl)
              <> ", dtype= "
              <> dtRepr
              <> " )"
      return $ EdhString colRepr

    colShowProc :: Edh EdhValue
    colShowProc = withThisColumn $ \this (SomeColumn _ !col) -> do
      (cs, cl) <- liftEIO $ view'column'data col
      !dto <- getColumnDtype this
      !dtRepr <- edhObjReprM dto
      let colRepr =
            "Column( capacity= "
              <> T.pack (show $ array'capacity cs)
              <> ", length= "
              <> T.pack (show cl)
              <> ", dtype= "
              <> dtRepr
              <> " )"

          readElem i = do
            !hv <- liftIO $ array'reader cs i
            toEdh hv >>= edhValueStrM

      !contentLines <- showColContent cl readElem
      return $ EdhString $ colRepr <> "\n" <> contentLines

    -- TODO impl. this following:
    --      https://pandas.pydata.org/pandas-docs/stable/reference/api/pandas.Series.describe.html
    colDescProc :: Edh EdhValue
    colDescProc = withThisColumn $ \this (SomeColumn _ !col) -> do
      (cs, cl) <- liftEIO $ view'column'data col
      !dto <- getColumnDtype this
      !dtRepr <- edhObjReprM dto
      let colRepr =
            "Column( capacity= "
              <> T.pack (show $ array'capacity cs)
              <> ", length= "
              <> T.pack (show cl)
              <> ", dtype= "
              <> dtRepr
              <> " )"

      return $
        EdhString $
          " 🚧 Statistical Description of Column data,\n"
            <> " 🏗  like Pandas' describe(), is yet to be implemented.\n"
            <> colRepr

    colIdxReadProc :: EdhValue -> Edh EdhValue
    colIdxReadProc !idxVal = withThisColumn $ \this !col -> do
      let withBoolIdx ::
            forall c f.
            ManagedColumn c f YesNo =>
            Object ->
            c YesNo ->
            Edh EdhValue
          withBoolIdx _ !idxCol =
            liftEIO (extractColumnBool this col idxCol) >>= \(!newColObj, _newCol) ->
              return $ EdhObject newColObj

          withIntpIdx ::
            forall c f.
            ManagedColumn c f Int =>
            Object ->
            c Int ->
            Edh EdhValue
          withIntpIdx _ !idxCol =
            liftEIO (extractColumnFancy this col idxCol) >>= \(!newColObj, _newCol) ->
              return $ EdhObject newColObj

          withEdhIdx :: Edh EdhValue
          withEdhIdx = do
            that <-
              edh'scope'that . contextScope . edh'context
                <$> edhThreadState
            parseEdhIndexM idxVal >>= \case
              Left !err -> throwEdhM UsageError err
              Right !idx -> case idx of
                EdhIndex !i -> case col of
                  SomeColumn _ col' -> do
                    (!cs, _cl) <- liftEIO $ view'column'data col'
                    !ev <- liftIO $ array'reader cs i
                    toEdh ev
                EdhAny -> return $ EdhObject that
                EdhAll -> return $ EdhObject that
                EdhSlice !start !stop !step -> case col of
                  SomeColumn _ col' -> do
                    (_cs, !cl) <- liftEIO $ view'column'data col'
                    (!iStart, !iStop, !iStep) <-
                      regulateEdhSliceM cl (start, stop, step)
                    (!newColObj, _newCol) <-
                      liftEIO $ sliceColumn this col iStart iStop iStep
                    return $ EdhObject newColObj

      withColumnOf' @YesNo idxVal withBoolIdx
        <|> withColumnOf' @Int idxVal withIntpIdx
        <|> withEdhIdx

    colIdxWriteProc :: EdhValue -> EdhValue -> Edh EdhValue
    colIdxWriteProc !idxVal !other = withThisColumn $ \_this !col -> do
      idxAssignColumn col idxVal other
      return other

    colCopyProc :: "capacity" ?: Int -> Edh EdhValue
    colCopyProc (optionalArg -> !maybeCap) = withThisColumn $
      \this (SomeColumn _ !col) -> do
        !cl <- liftEIO $ read'column'length col
        (disp, col') <-
          liftEIO $ copy'column'slice col (fromMaybe cl maybeCap) 0 cl 1
        case disp of
          StayComposed -> do
            !newColObj <- mutCloneHostObjectM this this col'
            return $ EdhObject newColObj
          ExtractAlone -> do
            !dto <- getColumnDtype this
            !newColObj <-
              createHostObjectM'
                (edh'obj'class this)
                (toDyn col')
                [dto]
            return $ EdhObject newColObj

    colDtypeProc :: Edh EdhValue
    colDtypeProc = do
      !this <- edh'scope'this . contextScope . edh'context <$> edhThreadState
      EdhObject <$> getColumnDtype this

arangeProc ::
  Object ->
  Object ->
  "rangeSpec" !: EdhValue ->
  "dtype" ?: Object ->
  Edh EdhValue
arangeProc
  !defaultDt
  !colClass
  (mandatoryArg -> !rngSpec)
  (defaultArg defaultDt -> !dto) =
    parseEdhIndexM (edhUltimate rngSpec) >>= \case
      Right (EdhIndex !stop)
        | stop >= 0 -> createRangeCol 0 stop 1
      Right (EdhSlice !start (Just !stopN) !step) -> do
        let !startN = fromMaybe 0 start
        createRangeCol startN stopN $
          fromMaybe (if stopN >= startN then 1 else -1) step
      Left !err ->
        edhSimpleDescM rngSpec >>= \ !rngDesc ->
          throwEdhM UsageError $ "invalid range " <> rngDesc <> " - " <> err
      _ ->
        edhSimpleDescM rngSpec >>= \ !rngDesc ->
          throwEdhM UsageError $ "invalid range " <> rngDesc
    where
      notNumDt dti = throwEdhM UsageError $ "not a numeric dtype: " <> dti

      createRangeCol :: Int -> Int -> Int -> Edh EdhValue
      createRangeCol !start !stop !step =
        if (stop > start && step <= 0) || (stop < start && step >= 0)
          then throwEdhM UsageError "range is not converging"
          else do
            let (q, r) = quotRem (stop - start) step
                !len = if r == 0 then abs q else 1 + abs q
            withDataType dto $ \case
              DeviceDt (dt :: DeviceDataType a) ->
                (<|> notNumDt (device'data'type'ident dt)) $ do
                  !fp <- with'num'device'data'type dt $
                    liftIO $ do
                      !p <- callocArray @a len
                      !fp <- newForeignPtr finalizerFree p
                      let fillRng :: Int -> Int -> IO ()
                          fillRng !n !i =
                            if i >= len
                              then return ()
                              else do
                                pokeElemOff p i $ fromIntegral n
                                fillRng (n + step) (i + 1)
                      fillRng start 0
                      return fp

                  let !cs = DeviceArray len fp
                  !csv <- newTMVarEdh cs
                  !clv <- newTVarEdh len
                  let !col = InMemDevCol csv clv
                  EdhObject
                    <$> createHostObjectM'
                      colClass
                      (toDyn $ someColumn col)
                      [dto]
              DirectDt (dt :: DirectDataType a) -> do
                let tryNumDt :: Edh EdhValue
                    tryNumDt =
                      with'num'direct'data'type dt $ do
                        !iov <- liftIO $ do
                          (iov :: MV.IOVector a) <- MV.new len
                          let fillRng :: Int -> Int -> IO ()
                              fillRng !n !i =
                                if i >= len
                                  then return ()
                                  else do
                                    MV.unsafeWrite iov i $ fromIntegral n
                                    fillRng (n + step) (i + 1)
                          fillRng start 0
                          return iov

                        let !cs = DirectArray iov
                        !csv <- newTMVarEdh cs
                        !clv <- newTVarEdh len
                        let !col = InMemDirCol csv clv
                        EdhObject
                          <$> createHostObjectM'
                            colClass
                            (toDyn $ someColumn col)
                            [dto]

                    tryFromDec :: Edh EdhValue
                    tryFromDec = (<|> notNumDt (direct'data'type'ident dt)) $
                      with'num'seed'direct'data'type dt $ \ !fromDec -> do
                        !iov <- liftIO $ do
                          (iov :: MV.IOVector a) <- MV.new len
                          let fillRng :: Int -> Int -> IO ()
                              fillRng !n !i =
                                if i >= len
                                  then return ()
                                  else do
                                    MV.unsafeWrite iov i $
                                      fromDec $ fromIntegral n
                                    fillRng (n + step) (i + 1)
                          fillRng start 0
                          return iov

                        let !cs = DirectArray iov
                        !csv <- newTMVarEdh cs
                        !clv <- newTVarEdh len
                        let !col = InMemDirCol csv clv
                        EdhObject
                          <$> createHostObjectM'
                            colClass
                            (toDyn $ someColumn col)
                            [dto]

                tryNumDt <|> tryFromDec
              DummyDt dti ->
                naM $ "you don't create arange Column of dummy dtype: " <> dti

randomProc ::
  Object ->
  Object ->
  "size" !: Int ->
  "rangeSpec" ?: EdhValue ->
  "dtype" ?: Object ->
  Edh EdhValue
randomProc
  !defaultDt
  !colClass
  (mandatoryArg -> !size)
  (defaultArg (EdhDecimal 1) -> !rngSpec)
  (defaultArg defaultDt -> !dto) = case edhUltimate rngSpec of
    EdhRange !lower !upper ->
      createRandomCol (edhBoundValue lower) (edhBoundValue upper)
    _ ->
      parseEdhIndexM (edhUltimate rngSpec) >>= \case
        Right (EdhIndex !stop) ->
          createRandomCol (EdhDecimal 0) (EdhDecimal $ fromIntegral stop)
        Right (EdhSlice !start (Just !stopN) Nothing) ->
          createRandomCol
            (EdhDecimal $ fromIntegral $ fromMaybe 0 start)
            (EdhDecimal $ fromIntegral stopN)
        Left !err ->
          edhValueDescM rngSpec >>= \ !rngDesc ->
            throwEdhM UsageError $
              "invalid random range " <> rngDesc <> " - " <> err
        _ ->
          edhValueDescM rngSpec >>= \ !rngDesc ->
            throwEdhM UsageError $
              "invalid random range " <> rngDesc
    where
      notRndDt dti = throwEdhM UsageError $ "not a numeric dtype: " <> dti

      createRandomCol :: EdhValue -> EdhValue -> Edh EdhValue
      createRandomCol !lowerValue !upperValue = do
        withDataType dto $ \case
          DeviceDt (dt :: DeviceDataType a) ->
            (<|> notRndDt (device'data'type'ident dt)) $
              with'random'device'data'type dt $ do
                !lower <- fromEdh @a lowerValue
                !upper <- fromEdh @a upperValue
                if lower == upper
                  then throwEdhM UsageError "random range is zero-width"
                  else do
                    !fp <- liftIO $ do
                      let (!lower', !upper') =
                            if lower < upper
                              then (lower, upper)
                              else (upper, lower)
                      !p <- callocArray @a size
                      !fp <- newForeignPtr finalizerFree p
                      let fillRng :: Int -> IO ()
                          fillRng !i =
                            if i >= size
                              then return ()
                              else do
                                pokeElemOff p i =<< randomRIO (lower', upper')
                                fillRng (i + 1)
                      fillRng 0
                      return fp

                    let !cs = DeviceArray size fp
                    !csv <- newTMVarEdh cs
                    !clv <- newTVarEdh size
                    let !col = InMemDevCol csv clv
                    EdhObject
                      <$> createHostObjectM'
                        colClass
                        (toDyn $ someColumn col)
                        [dto]
          DirectDt (dt :: DirectDataType a) ->
            (<|> notRndDt (direct'data'type'ident dt)) $
              with'random'direct'data'type dt $ do
                !lower <- fromEdh @a lowerValue
                !upper <- fromEdh @a upperValue
                if lower == upper
                  then throwEdhM UsageError "random range is zero-width"
                  else do
                    !iov <- liftIO $ do
                      let (!lower', !upper') =
                            if lower < upper
                              then (lower, upper)
                              else (upper, lower)
                      (iov :: MV.IOVector a) <- MV.new size
                      let fillRng :: Int -> IO ()
                          fillRng !i =
                            if i >= size
                              then return ()
                              else do
                                MV.unsafeWrite iov i
                                  =<< randomRIO (lower', upper')
                                fillRng (i + 1)
                      fillRng 0
                      return iov

                    let !cs = DirectArray iov
                    !csv <- newTMVarEdh cs
                    !clv <- newTVarEdh size
                    let !col = InMemDirCol csv clv
                    EdhObject
                      <$> createHostObjectM'
                        colClass
                        (toDyn $ someColumn col)
                        [dto]
          DummyDt dti ->
            naM $ "you don't create random Column of dummy dtype: " <> dti

-- TODO impl. `linspace` following:
--      https://numpy.org/doc/stable/reference/generated/numpy.linspace.html
-- Note it can be more exact by stepping with LosslessDecimal

-- | resemble https://numpy.org/doc/stable/reference/generated/numpy.where.html
whereProc :: Object -> Object -> ArgsPack -> Edh EdhValue
whereProc !colClass !dtIntp (ArgsPack [EdhObject !colYesNo] !kwargs)
  | odNull kwargs = (<|> throwEdhM UsageError "not a `yesno` column") $
    withColumnOf @YesNo colYesNo $ \_ !col -> do
      (cs, cl) <- liftEIO $ view'column'data col
      (!len, !fp) <- liftIO $ do
        !p <- callocArray @Int cl
        !fp <- newForeignPtr finalizerFree p
        let fillIdxs :: Int -> Int -> IO Int
            fillIdxs !n !i =
              if i >= cl
                then return n
                else
                  array'reader cs i >>= \case
                    YesNo 0 -> fillIdxs n (i + 1)
                    _ -> do
                      pokeElemOff p n i
                      fillIdxs (n + 1) (i + 1)
        (,fp) <$> fillIdxs 0 0

      let !cs' = DeviceArray cl fp
      !csv <- newTMVarEdh cs'
      !clv <- newTVarEdh len
      let !col' = InMemDevCol csv clv
      EdhObject
        <$> createHostObjectM'
          colClass
          (toDyn $ someColumn col')
          [dtIntp]
whereProc
  _colClass
  _dtIntp
  (ArgsPack [EdhObject !_colBoolIdx, !_trueData, !_falseData] !kwargs)
    | odNull kwargs = throwEdhM UsageError "not implemented yet."
whereProc _colClass _dtIntp !apk =
  throwEdhM UsageError $ "invalid args to where()" <> T.pack (show apk)
