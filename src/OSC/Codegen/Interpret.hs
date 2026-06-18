{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}

module OSC.Codegen.Interpret where

import Control.Applicative ((<|>))
import Control.Monad (forM_, when)
import Control.Monad.ST
import Control.Monad.Reader as R
import Data.STRef

import OSC.Expr.Comp
import OSC.Codegen
import OSC.Expr.Defunc hiding (const)
import qualified Data.Map as M
import Data.Bits ((.&.), (.|.), xor, shiftL, shiftR, rotateL, rotateR)
import Data.Map (Map)
import Data.Maybe (fromMaybe)

import Debug.Trace

data Value = VNumber Number | VArr [Number]
  deriving Show

data ExecEnv s = ExecEnv
  { globals :: Map Location (STRef s Value)
  , locals :: Map Location (STRef s Value)
  , funcMap :: Map FuncRef ProgramFunc
  }

type InterpretM s = ReaderT (ExecEnv s) (ST s)

numZeroValue :: TNumber -> Number
numZeroValue TI32 = I32 0
numZeroValue TF32 = F32 0
numZeroValue TI64 = I64 0
numZeroValue TF64 = F64 0

zeroValue :: Type -> Value
zeroValue (TNumber typ) = VNumber $ numZeroValue typ
zeroValue typ@(TArr _ _) = VArr (replicate count (numZeroValue bt))
  where
    bt = baseType typ
    count = elemCountOfType typ
zeroValue (TLam _ _) = VNumber (I32 0)

-- Helper function to copy the sign from one float to another
copySign :: (RealFloat a) => a -> a -> a
copySign x y = if signum y < 0 then negate (abs x) else abs x

applyOp :: Op -> Value -> Value -> Value
applyOp Add (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (a + b))
applyOp Add (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I64 (a + b))
applyOp Add (VNumber (F32 a)) (VNumber (F32 b)) = VNumber (F32 (a + b))
applyOp Add (VNumber (F64 a)) (VNumber (F64 b)) = VNumber (F64 (a + b))
applyOp Sub (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (a - b))
applyOp Sub (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I64 (a - b))
applyOp Sub (VNumber (F32 a)) (VNumber (F32 b)) = VNumber (F32 (a - b))
applyOp Sub (VNumber (F64 a)) (VNumber (F64 b)) = VNumber (F64 (a - b))
applyOp Mul (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (a * b))
applyOp Mul (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I64 (a * b))
applyOp Mul (VNumber (F32 a)) (VNumber (F32 b)) = VNumber (F32 (a * b))
applyOp Mul (VNumber (F64 a)) (VNumber (F64 b)) = VNumber (F64 (a * b))
applyOp Div (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (a `div` b))
applyOp Div (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I64 (a `div` b))
applyOp Div (VNumber (F32 a)) (VNumber (F32 b)) = VNumber (F32 (a / b))
applyOp Div (VNumber (F64 a)) (VNumber (F64 b)) = VNumber (F64 (a / b))
applyOp Mod (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (a `mod` b))
applyOp Mod (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I64 (a `mod` b))
applyOp Rem (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (a `rem` b))
applyOp Rem (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I64 (a `rem` b))
applyOp Rem (VNumber (F32 a)) (VNumber (F32 b)) = VNumber (F32 (snd (properFraction (a / b)) * b))
applyOp Rem (VNumber (F64 a)) (VNumber (F64 b)) = VNumber (F64 (snd (properFraction (a / b)) * b))
applyOp Eq (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (if a == b then 1 else 0))
applyOp Eq (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I32 (if a == b then 1 else 0))
applyOp Eq (VNumber (F32 a)) (VNumber (F32 b)) = VNumber (I32 (if a == b then 1 else 0))
applyOp Eq (VNumber (F64 a)) (VNumber (F64 b)) = VNumber (I32 (if a == b then 1 else 0))
applyOp Ne (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (if a /= b then 1 else 0))
applyOp Ne (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I32 (if a /= b then 1 else 0))
applyOp Ne (VNumber (F32 a)) (VNumber (F32 b)) = VNumber (I32 (if a /= b then 1 else 0))
applyOp Ne (VNumber (F64 a)) (VNumber (F64 b)) = VNumber (I32 (if a /= b then 1 else 0))
applyOp Gt (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (if a > b then 1 else 0))
applyOp Gt (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I32 (if a > b then 1 else 0))
applyOp Gt (VNumber (F32 a)) (VNumber (F32 b)) = VNumber (I32 (if a > b then 1 else 0))
applyOp Gt (VNumber (F64 a)) (VNumber (F64 b)) = VNumber (I32 (if a > b then 1 else 0))
applyOp Lt (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (if a < b then 1 else 0))
applyOp Lt (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I32 (if a < b then 1 else 0))
applyOp Lt (VNumber (F32 a)) (VNumber (F32 b)) = VNumber (I32 (if a < b then 1 else 0))
applyOp Lt (VNumber (F64 a)) (VNumber (F64 b)) = VNumber (I32 (if a < b then 1 else 0))
applyOp GEt (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (if a >= b then 1 else 0))
applyOp GEt (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I32 (if a >= b then 1 else 0))
applyOp GEt (VNumber (F32 a)) (VNumber (F32 b)) = VNumber (I32 (if a >= b then 1 else 0))
applyOp GEt (VNumber (F64 a)) (VNumber (F64 b)) = VNumber (I32 (if a >= b then 1 else 0))
applyOp LEt (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (if a <= b then 1 else 0))
applyOp LEt (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I32 (if a <= b then 1 else 0))
applyOp LEt (VNumber (F32 a)) (VNumber (F32 b)) = VNumber (I32 (if a <= b then 1 else 0))
applyOp LEt (VNumber (F64 a)) (VNumber (F64 b)) = VNumber (I32 (if a <= b then 1 else 0))
applyOp Min (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (min a b))
applyOp Min (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I64 (min a b))
applyOp Min (VNumber (F32 a)) (VNumber (F32 b)) = VNumber (F32 (min a b))
applyOp Min (VNumber (F64 a)) (VNumber (F64 b)) = VNumber (F64 (min a b))
applyOp Max (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (max a b))
applyOp Max (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I64 (max a b))
applyOp Max (VNumber (F32 a)) (VNumber (F32 b)) = VNumber (F32 (max a b))
applyOp Max (VNumber (F64 a)) (VNumber (F64 b)) = VNumber (F64 (max a b))
applyOp And (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (a .&. b))
applyOp And (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I64 (a .&. b))
applyOp Or (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (a .|. b))
applyOp Or (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I64 (a .|. b))
applyOp Xor (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (a `xor` b))
applyOp Xor (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I64 (a `xor` b))
applyOp Shl (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (a `shiftL` fromIntegral b))
applyOp Shl (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I64 (a `shiftL` fromIntegral b))
applyOp Shr (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (a `shiftR` fromIntegral b))
applyOp Shr (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I64 (a `shiftR` fromIntegral b))
applyOp Rotl (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (a `rotateL` fromIntegral b))
applyOp Rotl (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I64 (a `rotateL` fromIntegral b))
applyOp Rotr (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (a `rotateR` fromIntegral b))
applyOp Rotr (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I64 (a `rotateR` fromIntegral b))
applyOp CopySign (VNumber (F32 a)) (VNumber (F32 b)) = VNumber (F32 (copySign a b))
applyOp CopySign (VNumber (F64 a)) (VNumber (F64 b)) = VNumber (F64 (copySign a b))
applyOp op a b = error $ "applyOp: unsupported operation: " <> show a <> " " <> show op <> " " <> show b

-- Get a value from a location
getVar :: Location -> InterpretM s Value
getVar loc = do
  env <- ask
  case M.lookup loc env.locals <|> M.lookup loc env.globals of
    Just ref -> lift $ readSTRef ref
    Nothing -> error $ "getVar: location not found: " <> show loc

-- Set a value at a location
setVar :: Location -> Value -> InterpretM s ()
setVar loc val = do
  env <- ask
  case M.lookup loc env.locals <|> M.lookup loc env.globals of
    Just ref -> lift $ writeSTRef ref val
    Nothing -> error $ "setVar: location not found: " <> show loc

-- Extract a slice from a value
extractSlice :: Type -> Value -> Int -> Int -> Value
extractSlice (TArr _ _) (VArr vals) offset len = VArr (take len (drop offset vals))
extractSlice (TNumber _) (VArr vals) offset 1 = VNumber $ head (drop offset vals)
extractSlice _ (VNumber n) 0 1 = VNumber n
extractSlice typ v offset len = error $ "extractSlice: invalid slice of type " <> show typ <> ": " <> show offset <> ".." <> show (offset + len) <> " of " <> show v

-- Write a slice into a value
writeSlice :: Value -> Int -> Value -> Value
writeSlice (VArr dest) offset (VArr src) =
  let (before, rest) = splitAt offset dest
      after = drop (length src) rest
  in VArr (before <> src <> after)
writeSlice (VArr dest) offset (VNumber n) =
  let (before, _:after) = splitAt offset dest
  in VArr (before <> [n] <> after)
writeSlice _ _ v = v

-- Read a slice value from the execution context
readSlice :: Slice -> Map Captured (STRef s Value) -> Maybe (STRef s Value) -> InterpretM s Value
-- readSlice slice _ _
--   | trace ("SLICE: " <> show slice) False = undefined
readSlice (SConst n) _ _ = pure $ VNumber n
readSlice (SFuncRef (FuncRef fr)) _ _ = pure $ VNumber (I32 fr)
readSlice (SSlice typ (SArg arg) (Left offset) len) args _ = do
  case M.lookup arg args of
    Just ref -> do
      val <- lift $ readSTRef ref
      pure $ extractSlice typ val offset len
    Nothing -> error $ "readSlice: arg not found: " <> show arg
readSlice (SSlice typ (SVar loc) (Left offset) len) _ _ = do
  val <- getVar loc
  pure $ extractSlice typ val offset len
readSlice (SSlice typ (SVar loc) (Right offsetLoc) len) _ _ = do
  offsetVal <- getVar offsetLoc
  let offset = case offsetVal of
        VNumber (I32 i) -> fromIntegral i
        VNumber (I64 i) -> fromIntegral i
        _ -> error "readSlice: offset must be integer"
  val <- getVar loc
  pure $ extractSlice typ val offset len
readSlice (SSlice typ SRet (Left offset) len) _ (Just retRef) = do
  retVal <- lift $ readSTRef retRef
  pure $ extractSlice typ retVal offset len
readSlice (SSlice typ SRet (Right offsetLoc) len) _ (Just retRef) = do
  offsetVal <- getVar offsetLoc
  let offset = case offsetVal of
        VNumber (I32 i) -> fromIntegral i
        VNumber (I64 i) -> fromIntegral i
        _ -> error "readSlice: offset must be integer"
  retVal <- lift $ readSTRef retRef
  pure $ extractSlice typ retVal offset len
readSlice slice _ _ = error $ "readSlice: invalid slice: " <> show slice

-- Write a slice value to the execution context
writeSliceCtx :: String -> Slice -> Value ->  Maybe (STRef s Value) -> InterpretM s ()
writeSliceCtx _ (SSlice _ (SVar loc) (Left offset) _) val _ = do
  current <- getVar loc
  let updated = writeSlice current offset val
  setVar loc updated
writeSliceCtx _ (SSlice _ (SVar loc) (Right offsetLoc) _) val _ = do
  offsetVal <- getVar offsetLoc
  let offset = case offsetVal of
        VNumber (I32 i) -> fromIntegral i
        VNumber (I64 i) -> fromIntegral i
        _ -> error "writeSliceCtx: offset must be integer"
  current <- getVar loc
  let updated = writeSlice current offset val
  setVar loc updated
writeSliceCtx _ (SSlice _ SRet (Left offset) _) val (Just retRef) = do
  retVal <- lift $ readSTRef retRef
  lift $ writeSTRef retRef (writeSlice retVal offset val)
writeSliceCtx _ (SSlice _ SRet (Right offsetLoc) _) val (Just retRef) = do
  offsetVal <- getVar offsetLoc
  let offset = case offsetVal of
        VNumber (I32 i) -> fromIntegral i
        VNumber (I64 i) -> fromIntegral i
        _ -> error "writeSliceCtx: offset must be integer"
  retVal <- lift $ readSTRef retRef
  lift $ writeSTRef retRef (writeSlice retVal offset val)
writeSliceCtx callSite slice _ _ = error $ "writeSliceCtx [" <> callSite <> "]: invalid destination slice: " <> show slice

-- Interpret instructions with arguments and return value
interpInstrs :: [Instruction] -> Map Captured (STRef s Value) -> Maybe (STRef s Value) -> InterpretM s ()
interpInstrs [] _ _ = pure ()
interpInstrs (instr:instrs) args retRef = do
  case instr of
    ICopy dest src -> do
      srcVal <- readSlice src args retRef
      writeSliceCtx "ICopy" dest srcVal retRef
      interpInstrs instrs args retRef

    IBinOp op dest a b -> do
      aVal <- readSlice a args retRef
      bVal <- readSlice b args retRef
      let resultVal = applyOp op aVal bVal
      writeSliceCtx "IBinOp" dest resultVal retRef
      interpInstrs instrs args retRef

    IIf cond thn els -> do
      condVal <- readSlice cond args retRef
      let branch = case condVal of
            VNumber (I32 x) -> if x > 0 then thn else els
            VNumber (I64 x) -> if x > 0 then thn else els
            c -> error $ show c
      interpInstrs branch args retRef
      interpInstrs instrs args retRef

    ICall retSlice funcSlice argSlices -> do
      fr <- case funcSlice of
        SFuncRef fr -> pure fr
        _ -> do
          funcVal <- readSlice funcSlice args retRef
          case funcVal of
            VNumber (I32 fr) -> pure $ FuncRef fr
            _ -> error "ICall: function reference must be i32"

      env <- ask
      case M.lookup fr env.funcMap of
        Just func -> do
          -- Allocate and populate argument refs
          argRefs <- lift $ M.fromList <$> sequence
            [ do
                val <- runReaderT (readSlice argSlice args retRef) env
                ref <- newSTRef val
                pure (arg, ref)
            | (argSlice, (arg, _)) <- zip argSlices func.params
            ]
          
          -- Allocate locals for the function
          funcLocalRefs <- lift $ M.fromList <$> sequence
            [ do
                ref <- newSTRef (zeroValue typ)
                pure (loc, ref)
            | (loc, typ) <- M.toList func.locals
            ]
          
          -- Allocate return value based on slice type
          let retType = case retSlice of
                SSlice typ _ _ _ -> typ
                _ -> error "ICall: return must be a slice"
          funcRetRef <- lift $ newSTRef (zeroValue retType)
          
          -- Execute function with new local environment
          R.local (\ExecEnv {..} -> ExecEnv { locals = funcLocalRefs, .. }) $
            interpInstrs func.instructions argRefs (Just funcRetRef)
          
          -- Copy return value to destination
          finalRet <- lift $ readSTRef funcRetRef
          writeSliceCtx "ICall" retSlice finalRet retRef
          interpInstrs instrs args retRef
        Nothing -> error $ "ICall: function not found: " <> show fr

    IFor counterLoc initial steps step body -> do
      let loop i
            | step > 0 && i >= steps = pure ()
            | step < 0 && i <= steps = pure ()
            | step == 0 = pure ()  -- Avoid infinite loop
            | otherwise = do
                setVar counterLoc (VNumber (I32 i))
                interpInstrs body args retRef
                loop (i + step)
      loop initial
      interpInstrs instrs args retRef

-- Evaluate a reference to get its current value
evalRef :: Ref -> InterpretM s Value
evalRef (RConst n) = pure $ VNumber n
evalRef (RFuncRef _) = pure $ VNumber (I32 0)
evalRef (RVar _ loc) = getVar loc
evalRef projRef@(RProj _ _ _) = do
  valSlice <- toSlice ref
  idxVal <- evalRef idx

  _ <- trace (show projRef) (pure ())
  _ <- trace ("VAL: " <> show val) (pure ())
  _ <- trace ("OFFSET: " <> show idxVal) (pure ())
  let offset = case idxVal of
        VNumber (I32 i) -> fromIntegral i * innerDim
        VNumber (I64 i) -> fromIntegral i * innerDim
        _ -> error "evalRef: index must be integer"
  pure $ extractSlice (refType projRef) val offset innerDim
evalRef ref = error $ "evalRef: cannot evaluate ref at top level: " <> show ref

-- Interpret a program and generate a list of values
interpretToList :: Int -> Program -> [Value]
interpretToList n prog = runST $ do
  -- Allocate globals
  globalRefs <- M.fromList <$> sequence
    [ do
        ref <- newSTRef (zeroValue typ)
        pure (loc, ref)
    | (loc, typ) <- M.toList prog.globals
    ]
  
  let env = ExecEnv
        { globals = globalRefs
        , locals = M.empty
        , funcMap = prog.funcMap
        }
  
  -- Run startup instructions
  runReaderT (interpInstrs prog.startup M.empty Nothing) env
  
  -- Generate n values by calling eval then tick
  let go 0 = pure []
      go count = do
        runReaderT (interpInstrs prog.tick M.empty Nothing) env
        val <- runReaderT (evalRef prog.ref) env
        rest <- go (count - 1)
        pure (val : rest)
  
  go n
