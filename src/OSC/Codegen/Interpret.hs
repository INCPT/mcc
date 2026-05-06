{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}

module OSC.Codegen.Interpret where

import Control.Monad (replicateM, forM_, when)
import Control.Monad.State

import OSC.Expr.Comp
import OSC.Codegen
import OSC.Expr.Defunc hiding (const)
import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe (fromMaybe)

data Value = VNumber Number | VArr [Value]
  deriving Show

type VarTable = Map Location Value

data ExecState = ExecState
  { globals :: VarTable
  , funcMap :: Map FuncRef ProgramFunc
  }

type InterpM = State ExecState

zeroValue :: Type -> Value
zeroValue (TNumber TI32) = VNumber (I32 0)
zeroValue (TNumber TF32) = VNumber (F32 0)
zeroValue (TNumber TI64) = VNumber (I64 0)
zeroValue (TNumber TF64) = VNumber (F64 0)
zeroValue (TArr t dim) = VArr (replicate dim (zeroValue t))
zeroValue (TLam _ _) = VNumber (I32 0)

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

-- Allocate flattened array storage
allocateFlattened :: Type -> Value
allocateFlattened typ =
  let bt = baseType typ
      count = elemCountOfType typ
  in VArr (replicate count (zeroValue (TNumber bt)))

-- Get a value from a location
getVar :: Location -> VarTable -> Value
getVar loc vars = fromMaybe (error $ "getVar: location not found: " <> show loc) (M.lookup loc vars)

-- Set a value at a location
setVar :: Location -> Value -> VarTable -> VarTable
setVar = M.insert

-- Extract a slice from a value
extractSlice :: Value -> Int -> Int -> Value
extractSlice (VArr vals) offset len = VArr (take len (drop offset vals))
extractSlice (VNumber n) 0 1 = VNumber n
extractSlice v offset len = error $ "extractSlice: invalid slice " <> show offset <> ".." <> show (offset + len) <> " of " <> show v

-- Write a slice into a value
writeSlice :: Value -> Int -> Value -> Value
writeSlice (VArr dest) offset (VArr src) =
  let (before, rest) = splitAt offset dest
      after = drop (length src) rest
  in VArr (before <> src <> after)
writeSlice (VArr dest) offset (VNumber n) =
  let (before, _:after) = splitAt offset dest
  in VArr (before <> [VNumber n] <> after)
writeSlice _ _ _ = error "writeSlice: type mismatch"

-- Read a slice value from the execution context
readSlice :: Slice -> VarTable -> Map Captured Value -> Maybe Value -> Value
readSlice (SConst n) _ _ _ = VNumber n
readSlice (SFuncRef fr) _ _ _ = VNumber (I32 0) -- Function references as dummy values
readSlice (SSlice _ (SArg arg) (Left offset) len) _ args _ =
  case M.lookup arg args of
    Just val -> extractSlice val offset len
    Nothing -> error $ "readSlice: arg not found: " <> show arg
readSlice (SSlice _ (SVar loc) (Left offset) len) vars _ _ =
  extractSlice (getVar loc vars) offset len
readSlice (SSlice _ (SVar loc) (Right offsetLoc) len) vars _ _ =
  let VNumber offsetNum = getVar offsetLoc vars
      offset = case offsetNum of
        I32 i -> fromIntegral i
        I64 i -> fromIntegral i
        _ -> error "readSlice: offset must be integer"
  in extractSlice (getVar loc vars) offset len
readSlice (SSlice _ SRet (Left offset) len) _ _ (Just retVal) =
  extractSlice retVal offset len
readSlice (SSlice _ SRet (Right offsetLoc) len) vars _ (Just retVal) =
  let VNumber offsetNum = getVar offsetLoc vars
      offset = case offsetNum of
        I32 i -> fromIntegral i
        I64 i -> fromIntegral i
        _ -> error "readSlice: offset must be integer"
  in extractSlice retVal offset len
readSlice slice _ _ _ = error $ "readSlice: invalid slice: " <> show slice

-- Write a slice value to the execution context
writeSliceCtx :: Slice -> Value -> VarTable -> Map Captured Value -> Maybe Value -> (VarTable, Maybe Value)
writeSliceCtx (SSlice _ (SVar loc) (Left offset) _) val vars _ retVal =
  let current = getVar loc vars
      updated = writeSlice current offset val
  in (setVar loc updated vars, retVal)
writeSliceCtx (SSlice _ (SVar loc) (Right offsetLoc) _) val vars _ retVal =
  let VNumber offsetNum = getVar offsetLoc vars
      offset = case offsetNum of
        I32 i -> fromIntegral i
        I64 i -> fromIntegral i
        _ -> error "writeSliceCtx: offset must be integer"
      current = getVar loc vars
      updated = writeSlice current offset val
  in (setVar loc updated vars, retVal)
writeSliceCtx (SSlice _ SRet (Left offset) _) val vars _ (Just retVal) =
  (vars, Just (writeSlice retVal offset val))
writeSliceCtx (SSlice _ SRet (Right offsetLoc) _) val vars _ (Just retVal) =
  let VNumber offsetNum = getVar offsetLoc vars
      offset = case offsetNum of
        I32 i -> fromIntegral i
        I64 i -> fromIntegral i
        _ -> error "writeSliceCtx: offset must be integer"
  in (vars, Just (writeSlice retVal offset val))
writeSliceCtx slice _ _ _ _ = error $ "writeSliceCtx: invalid destination slice: " <> show slice

-- Interpret instructions with local variables, arguments, and return value
interpInstrs :: [Instruction] -> VarTable -> Map Captured Value -> Maybe Value -> InterpM (VarTable, Maybe Value)
interpInstrs [] locals _ retVal = pure (locals, retVal)
interpInstrs (instr:instrs) locals args retVal = do
  globs <- gets (.globals)
  let allVars = locals <> globs

  case instr of
    ICopy dest src -> do
      let srcVal = readSlice src allVars args retVal
      let (locals', retVal') = writeSliceCtx dest srcVal locals args retVal
      modify $ \ExecState {..} -> ExecState { globals = M.union locals' globals, .. }
      interpInstrs instrs locals' args retVal'

    IBinOp op dest a b -> do
      let aVal = readSlice a allVars args retVal
      let bVal = readSlice b allVars args retVal
      let resultVal = applyOp op aVal bVal
      let (locals', retVal') = writeSliceCtx dest resultVal locals args retVal
      modify $ \ExecState {..} -> ExecState { globals = M.union locals' globals, .. }
      interpInstrs instrs locals' args retVal'

    IIf cond thn els -> do
      let VNumber condVal = readSlice cond allVars args retVal
      let branch = case condVal of
            I32 0 -> els
            I64 0 -> els
            _ -> thn
      (locals', retVal') <- interpInstrs branch locals args retVal
      interpInstrs instrs locals' args retVal'

    ICall retSlice funcSlice argSlices -> do
      
      
      let fr = case funcSlice of
            SFuncRef fr -> fr
            slice -> let VNumber (I32 fr) = readSlice funcSlice allVars args retVal in FuncRef fr
              
      -- For now, just handle function calls by looking up in funcMap
      -- This is simplified - in reality we'd need to handle the function reference properly
      funcs <- gets (.funcMap)
      case M.lookup fr funcs of
        Just func -> do
          let argVals = M.fromList [ (arg, readSlice argSlice allVars args retVal) 
                                   | (argSlice, (arg, _)) <- zip argSlices func.params ]
          
          -- Allocate locals for the function
          let funcLocals = M.fromList [ (loc, allocateFlattened typ) | (loc, typ) <- M.toList func.locals ]
          
          -- Allocate return value based on slice type
          let retType = case retSlice of
                SSlice typ _ _ _ -> typ
                _ -> error "ICall: return must be a slice"
          let initialRet = allocateFlattened retType
          
          (_, mfinalRet) <- interpInstrs func.instructions funcLocals argVals (Just initialRet)
          
          case mfinalRet of
            Just finalRet -> do
              let (locals', retVal') = writeSliceCtx retSlice finalRet locals args retVal
              modify $ \ExecState {..} -> ExecState { globals = M.union locals' globals, .. }
              interpInstrs instrs locals' args retVal'
            Nothing -> error "finalRet"
        Nothing -> error $ "ICall: function not found: " <> show fr

    IFor counterLoc initial steps step body -> do
      let loop i locals' retVal'
            | i >= steps = pure (locals', retVal')
            | otherwise = do
                let locals'' = setVar counterLoc (VNumber (I32 i)) locals'
                modify $ \ExecState {..} -> ExecState { globals = M.union locals'' globals, .. }
                (locals''', retVal'') <- interpInstrs body locals'' args retVal'
                loop (i + step) locals''' retVal''
      (locals', retVal') <- loop initial locals retVal
      interpInstrs instrs locals' args retVal'

-- Evaluate a reference to get its current value
evalRef :: Ref -> InterpM Value
evalRef (RConst n) = pure $ VNumber n
evalRef (RFuncRef _) = pure $ VNumber (I32 0)
evalRef (RVar typ loc) = do
  globs <- gets (.globals)
  pure $ getVar loc globs
evalRef (RProj ref idx innerDim) = do
  val <- evalRef ref
  idxVal <- evalRef idx
  let VNumber idxNum = idxVal
  let offset = case idxNum of
        I32 i -> fromIntegral i * innerDim
        I64 i -> fromIntegral i * innerDim
        _ -> error "evalRef: index must be integer"
  pure $ extractSlice val offset innerDim
evalRef ref = error $ "evalRef: cannot evaluate ref at top level: " <> show ref

-- Initialize the interpreter with a program
initInterpreter :: Program -> (InterpM (), InterpM (), InterpM Value)
initInterpreter prog =
  let startup = do
        -- Allocate globals
        let globalVars = M.fromList [ (loc, allocateFlattened typ) | (loc, typ) <- M.toList prog.globals ]
        put $ ExecState { globals = globalVars, funcMap = prog.funcMap }
        
        -- Run startup instructions
        (_, _) <- interpInstrs prog.startup M.empty M.empty Nothing
        pure ()
      
      tick = do
        -- Run tick instructions
        (_, _) <- interpInstrs prog.tick M.empty M.empty Nothing
        pure ()
      
      eval = evalRef prog.ref
  
  in (startup, tick, eval)

-- Interpret a program and generate a list of values
interpretToList :: Program -> Int -> [Value]
interpretToList prog n =
  let (startup, tick, eval) = initInterpreter prog
      initialState = ExecState { globals = M.empty, funcMap = prog.funcMap }
      
      -- Run startup
      stateAfterStartup = execState startup initialState
      
      -- Generate n values by calling eval then tick
      go 0 st = []
      go count st =
        let (val, st') = runState eval st
            st'' = execState tick st'
        in val : go (count - 1) st''
  
  in go n stateAfterStartup
