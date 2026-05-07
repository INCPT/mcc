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

import Debug.Trace

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
applyOp op a b = error $ "applyOp: unsupported operation: " <> show a <> " " <> show op <> " " <> show b

-- Allocate flattened array storage
allocateFlattened :: Type -> Value
allocateFlattened typ@(TArr _ _) =
  let bt = baseType typ
      count = elemCountOfType typ
  in VArr (replicate count (zeroValue (TNumber bt)))
allocateFlattened typ = zeroValue typ

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
writeSlice _ _ v = v

-- Read a slice value from the execution context
readSlice :: Slice -> VarTable -> Map Captured Value -> Maybe Value -> Value
readSlice (SConst n) _ _ _ = VNumber n
readSlice (SFuncRef fr) _ _ _ = VNumber (I32 0) -- Function references as dummy values
readSlice (SSlice _ (SArg arg) (Left offset) len) _ args _ =
  case M.lookup arg args of
    Just val -> extractSlice val offset len
    Nothing -> error $ "readSlice: arg not found: " <> show arg
readSlice (SSlice _ (SVar loc) (Left offset) len) vars _ _ =
  let val = fromMaybe (error $ "readSlice: SVar (Left offset): location not found: " <> show loc) (M.lookup loc vars)
  in extractSlice val offset len
readSlice (SSlice _ (SVar loc) (Right offsetLoc) len) vars _ _ =
  let VNumber offsetNum = fromMaybe (error $ "readSlice: SVar (Right offsetLoc) - offsetLoc: location not found: " <> show offsetLoc) (M.lookup offsetLoc vars)
      offset = case offsetNum of
        I32 i -> fromIntegral i
        I64 i -> fromIntegral i
        _ -> error "readSlice: offset must be integer"
      val = fromMaybe (error $ "readSlice: SVar (Right offsetLoc) - loc: location not found: " <> show loc) (M.lookup loc vars)
  in extractSlice val offset len
readSlice (SSlice _ SRet (Left offset) len) _ _ (Just retVal) =
  extractSlice retVal offset len
readSlice (SSlice _ SRet (Right offsetLoc) len) vars _ (Just retVal) =
  let VNumber offsetNum = fromMaybe (error $ "readSlice: SRet (Right offsetLoc): location not found: " <> show offsetLoc) (M.lookup offsetLoc vars)
      offset = case offsetNum of
        I32 i -> fromIntegral i
        I64 i -> fromIntegral i
        _ -> error "readSlice: offset must be integer"
  in extractSlice retVal offset len
readSlice slice _ _ _ = error $ "readSlice: invalid slice: " <> show slice

-- Write a slice value to the execution context
-- Returns (updated locals, updated retVal)
-- Note: vars contains both locals and globals merged
writeSliceCtx :: String -> Slice -> Value -> VarTable -> Map Captured Value -> Maybe Value -> (VarTable, Maybe Value)
writeSliceCtx callSite (SSlice _ (SVar loc) (Left offset) _) val vars _ retVal =
  let current = fromMaybe (error $ "writeSliceCtx [" <> callSite <> "]: SVar (Left offset): location not found: " <> show loc <> ", available: " <> show (M.keys vars)) (M.lookup loc vars)
      updated = writeSlice current offset val
  in (setVar loc updated vars, retVal)
writeSliceCtx callSite (SSlice _ (SVar loc) (Right offsetLoc) _) val vars _ retVal =
  let VNumber offsetNum = fromMaybe (error $ "writeSliceCtx [" <> callSite <> "]: SVar (Right offsetLoc) - offsetLoc: location not found: " <> show offsetLoc <> ", available: " <> show (M.keys vars)) (M.lookup offsetLoc vars)
      offset = case offsetNum of
        I32 i -> fromIntegral i
        I64 i -> fromIntegral i
        _ -> error "writeSliceCtx: offset must be integer"
      current = fromMaybe (error $ "writeSliceCtx [" <> callSite <> "]: SVar (Right offsetLoc) - loc: location not found: " <> show loc <> ", available: " <> show (M.keys vars)) (M.lookup loc vars)
      updated = writeSlice current offset val
  in (setVar loc updated vars, retVal)
writeSliceCtx _ (SSlice _ SRet (Left offset) _) val vars _ (Just retVal) =
  (vars, Just (writeSlice retVal offset val))
writeSliceCtx callSite (SSlice _ SRet (Right offsetLoc) _) val vars _ (Just retVal) =
  let VNumber offsetNum = fromMaybe (error $ "writeSliceCtx [" <> callSite <> "]: SRet (Right offsetLoc): location not found: " <> show offsetLoc) (M.lookup offsetLoc vars)
      offset = case offsetNum of
        I32 i -> fromIntegral i
        I64 i -> fromIntegral i
        _ -> error "writeSliceCtx: offset must be integer"
  in (vars, Just (writeSlice retVal offset val))
writeSliceCtx callSite slice _ _ _ _ = error $ "writeSliceCtx [" <> callSite <> "]: invalid destination slice: " <> show slice

-- Interpret instructions with local variables, arguments, and return value
interpInstrs :: [Instruction] -> VarTable -> Map Captured Value -> Maybe Value -> InterpM (VarTable, Maybe Value)
interpInstrs [] locals _ retVal = pure (locals, retVal)
interpInstrs (instr:instrs) locals args retVal = trace (show instr) $ do
  globs <- gets (.globals)
  let allVars = locals <> globs

  case instr of
    ICopy dest src -> do
      let srcVal = readSlice src allVars args retVal
      let (allVars', retVal') = writeSliceCtx "ICopy" dest srcVal allVars args retVal
      -- Split back into locals and globals
      let (locals', globs') = M.partitionWithKey (\(Location region _) _ -> region == AllocLocal) allVars'
      modify $ \ExecState {..} -> ExecState { globals = globs', .. }
      interpInstrs instrs locals' args retVal'

    IBinOp op dest a b -> do
      let aVal = readSlice a allVars args retVal
      let bVal = readSlice b allVars args retVal
      let resultVal = applyOp op aVal bVal
      let (allVars', retVal') = writeSliceCtx "IBinOp" dest resultVal allVars args retVal
      -- Split back into locals and globals
      let (locals', globs') = M.partitionWithKey (\(Location region _) _ -> region == AllocLocal) allVars'
      modify $ \ExecState {..} -> ExecState { globals = globs', .. }
      interpInstrs instrs locals' args retVal'

    IIf cond thn els -> do
      let condVal = readSlice cond allVars args retVal
      let branch = case condVal of
            VNumber (I32 x) -> if x > 0 then thn else els
            VNumber (I64 x) -> if x > 0 then thn else els
            c -> error $ show c
      (locals', retVal') <- interpInstrs branch locals args retVal
      interpInstrs instrs locals' args retVal'

    ICall retSlice funcSlice argSlices -> trace ("FUNSLICE: " <> show funcSlice <> ", ALLVARS: " <> show allVars) $ do
      let fr = case funcSlice of
            SFuncRef fr -> fr
            slice -> let VNumber (I32 fr) = readSlice funcSlice allVars args retVal in FuncRef fr

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
              let (allVars', retVal') = writeSliceCtx "ICall" retSlice finalRet allVars args retVal
              -- Split back into locals and globals
              let (locals', globs') = M.partitionWithKey (\(Location region _) _ -> region == AllocLocal) allVars'
              modify $ \ExecState {..} -> ExecState { globals = globs', .. }
              interpInstrs instrs locals' args retVal'
            Nothing -> error "finalRet"
        Nothing -> error $ "ICall: function not found: " <> show fr

    IFor counterLoc initial steps step body -> do
      let loop i locals' retVal'
            | step > 0 && i >= steps = pure (locals', retVal')
            | step < 0 && i <= steps = pure (locals', retVal')
            | step == 0 = pure (locals', retVal')  -- Avoid infinite loop
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
  pure $ fromMaybe (error $ "evalRef: RVar: location not found: " <> show loc) (M.lookup loc globs)
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
