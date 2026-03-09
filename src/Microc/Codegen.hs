{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fno-defer-type-errors  #-}

module Microc.Codegen
  ( codegenProgram
  )
where

import           Language.Wasm.Structure

import qualified Data.Map                      as M
import           Control.Monad.State
import           Data.String.Conversions
import qualified Data.Text                     as T
import           Data.Text                      ( Text )
import           Data.Word                      ( Word32, Word64 )
import qualified Data.List                     as List
import           Data.Text.Encoding             ( encodeUtf8 )
import qualified Data.ByteString.Lazy          as LBS
import           Numeric.Natural                ( Natural )
import qualified Data.Text.Lazy                as TL

import           Microc.Sast
import           Microc.Ast                     ( Type(..)
                                                , Op(..)
                                                , Uop(..)
                                                , Bind(..)
                                                , Struct(..)
                                                )

-- Environment for tracking variables, functions, and types during codegen
data CodegenState = CodegenState {
    localMap :: M.Map Text LocalIndex,
    funcMap :: M.Map Text FuncIndex,
    typeMap :: M.Map FuncType TypeIndex,
    nextLocal :: LocalIndex,
    currentInstructions :: Expression,
    allTypes :: [FuncType],
    allFunctions :: [Function],
    allImports :: [Import],
    allExports :: [Export]
} deriving (Show, Eq)

type Codegen = State CodegenState

emptyState :: CodegenState
emptyState = CodegenState {
    localMap = M.empty,
    funcMap = M.empty,
    typeMap = M.empty,
    nextLocal = 0,
    currentInstructions = [],
    allTypes = [],
    allFunctions = [],
    allImports = [],
    allExports = []
}

-- Helper to emit instructions
emit :: Instruction Natural -> Codegen ()
emit instr = modify $ \s -> s { currentInstructions = currentInstructions s ++ [instr] }

-- Helper to get current instructions and reset
getInstructions :: Codegen Expression
getInstructions = do
    instrs <- gets currentInstructions
    modify $ \s -> s { currentInstructions = [] }
    return instrs

-- Get the WASM value type for a MicroC type
wasmType :: Type -> ValueType
wasmType TyInt = I32
wasmType TyChar = I32
wasmType TyBool = I32
wasmType TyFloat = F64
wasmType (Pointer _) = I32
wasmType TyVoid = error "Cannot get WASM type for void"
wasmType (TyStruct _) = error "Structs not yet supported in WASM codegen"

-- Get size in bytes of a type
sizeOf :: Type -> Natural
sizeOf TyInt = 4
sizeOf TyChar = 1
sizeOf TyBool = 1
sizeOf TyFloat = 8
sizeOf (Pointer _) = 4
sizeOf TyVoid = 0
sizeOf (TyStruct _) = error "Struct size calculation not yet implemented"

-- Get or create a type index for a function type
getTypeIndex :: FuncType -> Codegen TypeIndex
getTypeIndex ft = do
    tm <- gets typeMap
    case M.lookup ft tm of
        Just idx -> return idx
        Nothing -> do
            types <- gets allTypes
            let idx = fromIntegral $ length types
            modify $ \s -> s {
                allTypes = allTypes s ++ [ft],
                typeMap = M.insert ft idx (typeMap s)
            }
            return idx

-- Code generation for expressions
codegenSexpr :: SExpr -> Codegen ()
codegenSexpr (TyInt, SLiteral i) = emit $ I32Const (fromIntegral i)
codegenSexpr (TyFloat, SFliteral f) = emit $ F64Const f
codegenSexpr (TyBool, SBoolLit b) = emit $ I32Const (if b then 1 else 0)
codegenSexpr (TyChar, SCharLit c) = emit $ I32Const (fromIntegral $ fromEnum c)
codegenSexpr (Pointer TyChar, SStrLit _s) = do
    -- String literals would need data section support
    emit $ I32Const 0  -- Placeholder
codegenSexpr (_, SNull) = emit $ I32Const 0
codegenSexpr (TyInt, SSizeof t) = emit $ I32Const (fromIntegral $ sizeOf t)

codegenSexpr (_, LVal (SId name)) = do
    lm <- gets localMap
    case M.lookup name lm of
        Just idx -> emit $ GetLocal idx
        Nothing -> error $ "Variable not found: " ++ T.unpack name

codegenSexpr (_, SAssign (SId name) rhs) = do
    lm <- gets localMap
    case M.lookup name lm of
        Just idx -> do
            codegenSexpr rhs
            emit $ SetLocal idx
        Nothing -> error $ "Variable not found: " ++ T.unpack name

codegenSexpr (t, SBinop op lhs rhs) = do
    codegenSexpr lhs
    codegenSexpr rhs
    case op of
        Add -> case t of
            TyInt -> emit $ IBinOp BS32 IAdd
            TyFloat -> emit $ FBinOp BS64 FAdd
            _ -> error "Invalid type for Add"
        Sub -> case t of
            TyInt -> emit $ IBinOp BS32 ISub
            TyFloat -> emit $ FBinOp BS64 FSub
            _ -> error "Invalid type for Sub"
        Mult -> case t of
            TyInt -> emit $ IBinOp BS32 IMul
            TyFloat -> emit $ FBinOp BS64 FMul
            _ -> error "Invalid type for Mult"
        Div -> case t of
            TyInt -> emit $ IBinOp BS32 IDivS
            TyFloat -> emit $ FBinOp BS64 FDiv
            _ -> error "Invalid type for Div"
        Equal -> case fst lhs of
            TyInt -> emit $ IRelOp BS32 IEq
            TyBool -> emit $ IRelOp BS32 IEq
            TyChar -> emit $ IRelOp BS32 IEq
            TyFloat -> emit $ FRelOp BS64 FEq
            Pointer _ -> emit $ IRelOp BS32 IEq
            _ -> error "Invalid type for Equal"
        Neq -> case fst lhs of
            TyInt -> emit $ IRelOp BS32 INe
            TyBool -> emit $ IRelOp BS32 INe
            TyChar -> emit $ IRelOp BS32 INe
            TyFloat -> emit $ FRelOp BS64 FNe
            Pointer _ -> emit $ IRelOp BS32 INe
            _ -> error "Invalid type for Neq"
        Less -> case fst lhs of
            TyInt -> emit $ IRelOp BS32 ILtS
            TyChar -> emit $ IRelOp BS32 ILtU
            TyFloat -> emit $ FRelOp BS64 FLt
            _ -> error "Invalid type for Less"
        Leq -> case fst lhs of
            TyInt -> emit $ IRelOp BS32 ILeS
            TyChar -> emit $ IRelOp BS32 ILeU
            TyFloat -> emit $ FRelOp BS64 FLe
            _ -> error "Invalid type for Leq"
        Greater -> case fst lhs of
            TyInt -> emit $ IRelOp BS32 IGtS
            TyChar -> emit $ IRelOp BS32 IGtU
            TyFloat -> emit $ FRelOp BS64 FGt
            _ -> error "Invalid type for Greater"
        Geq -> case fst lhs of
            TyInt -> emit $ IRelOp BS32 IGeS
            TyChar -> emit $ IRelOp BS32 IGeU
            TyFloat -> emit $ FRelOp BS64 FGe
            _ -> error "Invalid type for Geq"
        And -> emit $ IBinOp BS32 IAnd
        Or -> emit $ IBinOp BS32 IOr
        BitAnd -> emit $ IBinOp BS32 IAnd
        BitOr -> emit $ IBinOp BS32 IOr
        _ -> error $ "Binary operator not yet implemented: " ++ show op

codegenSexpr (t, SUnop op e) = do
    codegenSexpr e
    case op of
        Neg -> case t of
            TyInt -> do
                emit $ I32Const 0
                emit $ IBinOp BS32 ISub
            TyFloat -> emit $ FUnOp BS64 FNeg
            _ -> error "Invalid type for Neg"
        Not -> emit I32Eqz

codegenSexpr (_, SCall fun es) = do
    fm <- gets funcMap
    mapM_ codegenSexpr es
    case M.lookup fun fm of
        Just idx -> emit $ Call idx
        Nothing -> error $ "Function not found: " ++ T.unpack fun

codegenSexpr (_, SNoexpr) = return ()

codegenSexpr sx = error $ "Expression not yet implemented: " ++ show sx

-- Code generation for statements
codegenStatement :: SStatement -> Codegen ()
codegenStatement (SExpr e) = codegenSexpr e
codegenStatement (SReturn e) = case e of
    (TyVoid, SNoexpr) -> emit Return
    _ -> codegenSexpr e >> emit Return
codegenStatement (SBlock ss) = mapM_ codegenStatement ss
codegenStatement _ = error "Statement not yet implemented"

-- Code generation for functions
codegenFunc :: SFunction -> Codegen FuncIndex
codegenFunc f = do
    -- Build function type
    let paramTypes = map (wasmType . bindType) (sformals f)
    let resultTypes = case styp f of
            TyVoid -> []
            t -> [wasmType t]
    let funcType = FuncType paramTypes resultTypes
    
    -- Get or create type index
    typeIdx <- getTypeIndex funcType
    
    -- Set up local variables (params + locals)
    let paramNames = map (\(Bind _ n) -> n) (sformals f)
    let localNames = map (\(Bind _ n) -> n) (slocals f)
    let allNames = paramNames ++ localNames
    let localIndices = M.fromList $ zip allNames [0..]
    
    -- Save current state and set up for this function
    oldLocalMap <- gets localMap
    modify $ \s -> s { localMap = localIndices, nextLocal = fromIntegral $ length allNames }
    
    -- Generate function body
    codegenStatement (sbody f)
    body <- getInstructions
    
    -- Restore state
    modify $ \s -> s { localMap = oldLocalMap }
    
    -- Create function
    let localTypes = map (wasmType . bindType) (slocals f)
    let func = Function {
        funcType = typeIdx,
        localTypes = localTypes,
        body = body
    }
    
    -- Add function to module
    funcs <- gets allFunctions
    let funcIdx = fromIntegral $ length funcs
    modify $ \s -> s { allFunctions = allFunctions s ++ [func] }
    
    return funcIdx

-- Main code generation entry point
codegenProgram :: SProgram -> Module
codegenProgram (_structs, _globals, funcs) = 
    let finalState = execState (mapM codegenFuncWithName funcs) emptyState
        
        -- Add memory import
        memImport = Import {
            sourceModule = TL.pack "env",
            name = TL.pack "memory",
            desc = ImportMemory (Limit 1 Nothing)
        }
        
        -- Find main function and create export
        mainExport = case List.findIndex (\f -> sname f == "main") funcs of
            Just idx -> [Export {
                name = TL.pack "main",
                desc = ExportFunc (fromIntegral idx)
            }]
            Nothing -> []
        
    in Module {
        types = allTypes finalState,
        functions = allFunctions finalState,
        tables = [],
        mems = [],
        globals = [],
        elems = [],
        datas = [],
        start = Nothing,
        imports = [memImport],
        exports = mainExport ++ allExports finalState
    }
  where
    codegenFuncWithName :: SFunction -> Codegen ()
    codegenFuncWithName f = do
        funcIdx <- codegenFunc f
        modify $ \s -> s { funcMap = M.insert (sname f) funcIdx (funcMap s) }
