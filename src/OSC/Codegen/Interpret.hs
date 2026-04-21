{-# LANGUAGE OverloadedRecordDot #-}

module OSC.Codegen.Interpret where

import Control.Monad (replicateM, forM_)

import OSC.Codegen
import qualified Data.Map as M
import Data.Map (Map)
import Control.Monad.State
import Data.Maybe (fromMaybe)

data Value = VNumber Number | VArr [Value]
  deriving Show

type VarTable = Map Idx Value

zeroValue :: Type -> Value
zeroValue (TNumber TI32) = VNumber (I32 0)
zeroValue (TNumber TF32) = VNumber (F32 0)
zeroValue (TNumber TI64) = VNumber (I64 0)
zeroValue (TNumber TF64) = VNumber (F64 0)
zeroValue (TArr t dim) = VArr (replicate dim (zeroValue t))
zeroValue (TAbs _ _) = VNumber (I32 0)

allocateVars :: [(Type, Idx)] -> VarTable
allocateVars allocs = M.fromList [ (idx, zeroValue t) | (t, idx) <- allocs ]

irInterpretToList :: Int -> IR -> Type -> FuncRef -> [Value]
irInterpretToList steps ir mainType mainFuncFR = evalState (replicateM steps runTick) globalTable
  where
    maxIdx = maximum [ idx | (_, Global idx) <- ir.globalAllocations ]
    retIdx = Global (maxIdx + 1)
    globalTable = allocateVars $ (mainType, Global (maxIdx + 1)):ir.globalAllocations
    mainFunc = ir.funcMap M.! mainFuncFR

    runFunc :: IRFunc -> [Ref] -> State VarTable ()
    runFunc func args = do
      let localTable = allocateVars func.allocations
      evalStateT (executeInstructions ir.tickFunc.instructions args) localTable

    runTick :: State VarTable Value
    runTick = do
      runFunc mainFunc [RVar retIdx]
      runFunc ir.tickFunc []
      gets (fromMaybe (error $ "readVar: global not found: " <> show retIdx) . M.lookup retIdx)

    executeInstructions :: [Instruction] -> [Ref] -> StateT VarTable (State VarTable) ()
    executeInstructions instrs args = mapM_ (executeInstruction args) instrs

    executeInstruction :: [Ref] -> Instruction -> StateT VarTable (State VarTable) ()
    executeInstruction args (SCopy _ src dst) = readRef args src >>= writeRef args dst

    executeInstruction args (SIf cond thn els) = do
      condVal <- readRef args cond
      case condVal of
        VNumber (I32 0) -> mapM_ (executeInstruction args) els
        VNumber (I64 0) -> mapM_ (executeInstruction args) els
        _ -> mapM_ (executeInstruction args) thn

    executeInstruction args (SCall funcRef argRefs retRef) = do
      v <- readRef args funcRef
      case v of
        VNumber (I32 frIdx) -> do
          let fr = FuncRef (fromIntegral frIdx)
          let irFunc = ir.funcMap M.! fr
          let localTable = allocateVars irFunc.allocations
          lift $ evalStateT (executeInstructions irFunc.instructions (argRefs <> [retRef])) localTable
        _ -> error $ "readRef: expected i32: " <> show v

    executeInstruction args (SBinOp op aRef bRef resRef) = do
      aVal <- readRef args aRef
      bVal <- readRef args bRef
      let resVal = applyOp op aVal bVal
      writeRef args resRef resVal

    executeInstruction args (SFor counterRef initial steps step body) = do
      forM_ [initial, initial + step .. initial + step * (steps - 1)] $ \i -> do
        writeRef args counterRef (VNumber (I32 i))
        mapM_ (executeInstruction args) body

    readRef :: [Ref] -> Ref -> StateT VarTable (State VarTable) Value
    readRef args (RArg n) = if n < length args
      then readRef args (args !! n)
      else error $ "readRef: " <> show args <> ", " <> show n
    readRef args RRet = readRef args (args !! (length args - 1))
    readRef _ (RConst n) = pure (VNumber n)
    readRef _ (RVar idx) = readVar idx
    readRef _ (RArr _ idx) = readVar idx
    readRef args (RProj ref idxRef) = do
      v <- readRef args idxRef
      case v of
        VNumber idx -> do
          val <- readRef args ref
          pure (projectValue val idx)
        _ -> error $ "readRef: expected number: " <> show v
    readRef _ (RFuncRef (FuncRef i)) = pure (VNumber (I32 (fromIntegral i)))
    readRef _ (RFuncRefRef idx) = readVar idx

    writeRef :: [Ref] -> Ref -> Value -> StateT VarTable (State VarTable) ()
    writeRef _ (RVar idx) val = writeVar idx val
    writeRef args RRet val = writeRef args (args !! (length args - 1)) val
    writeRef _ (RArr _ idx) val = writeVar idx val
    writeRef args (RProj ref idxRef) val = do
      v <- readRef args idxRef
      case v of
        VNumber idx -> do
          oldVal <- readRef args ref
          let newVal = updateValue oldVal idx val
          writeRef args ref newVal
        _ -> error $ "writeRef: expected number: " <> show v
    writeRef _ (RFuncRefRef idx) val = writeVar idx val
    writeRef _ ref _ = error $ "writeRef: invalid destination" <> show ref

    readVar :: Idx -> StateT VarTable (State VarTable) Value
    readVar idx@(Local _) = gets (fromMaybe (error $ "readVar: local not found: " <> show idx) . M.lookup idx)
    readVar idx@(Global _) = lift $ gets (fromMaybe (error $ "readVar: global not found: " <> show idx) . M.lookup idx)

    writeVar :: Idx -> Value -> StateT VarTable (State VarTable) ()
    writeVar idx@(Local _) val = modify (M.insert idx val)
    writeVar idx@(Global _) val = lift $ modify (M.insert idx val)

    projectValue :: Value -> Number -> Value
    projectValue (VArr vals) (I32 i) = vals !! fromIntegral i
    projectValue (VArr vals) (I64 i) = vals !! fromIntegral i
    projectValue _ _ = error "projectValue: invalid projection"

    updateValue :: Value -> Number -> Value -> Value
    updateValue (VArr vals) (I32 i) newVal = 
      let idx = fromIntegral i
      in VArr (take idx vals <> [newVal] <> drop (idx + 1) vals)
    updateValue (VArr vals) (I64 i) newVal = 
      let idx = fromIntegral i
      in VArr (take idx vals <> [newVal] <> drop (idx + 1) vals)
    updateValue _ _ _ = error "updateValue: invalid update"

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
    applyOp Eq (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (if a == b then 1 else 0))
    applyOp Eq (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I64 (if a == b then 1 else 0))
    applyOp Eq (VNumber (F32 a)) (VNumber (F32 b)) = VNumber (I32 (if a == b then 1 else 0))
    applyOp Eq (VNumber (F64 a)) (VNumber (F64 b)) = VNumber (I64 (if a == b then 1 else 0))
    applyOp _ _ _ = error "applyOp: unsupported operation"
