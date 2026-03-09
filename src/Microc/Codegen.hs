{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-defer-type-errors #-}

module Microc.Codegen
  ( codegenProgram
  )
where

-- import qualified LLVM.AST.IntegerPredicate     as IP
-- import qualified LLVM.AST.FloatingPointPredicate
--                                                as FP
-- import           LLVM.AST                       ( Operand )
-- import qualified LLVM.AST                      as AST
-- import qualified LLVM.AST.Float                as AST
-- import qualified LLVM.AST.Type                 as AST
-- import qualified LLVM.AST.Constant             as C
-- import           LLVM.AST.Name
-- import           LLVM.AST.Typed                 ( typeOf )
-- 
-- import qualified LLVM.IRBuilder.Module         as L
-- import qualified LLVM.IRBuilder.Monad          as L
-- import qualified LLVM.IRBuilder.Instruction    as L
-- import qualified LLVM.IRBuilder.Constant       as L
-- import           LLVM.Prelude                   ( ShortByteString )

import           Language.Wasm.Builder
import           Language.Wasm.Structure

import qualified Data.Map                      as M
import           Control.Monad.State
import           Data.Proxy
import           Data.String                    ( fromString )

import           Microc.Utils
import           Microc.Sast
import           Microc.Ast                     ( Type(..)
                                                , Op(..)
                                                , Uop(..)
                                                , Bind(..)
                                                , Struct(..)
                                                )

import           Data.String.Conversions
import qualified Data.Text                     as T
import           Data.Text                      ( Text )
import           Data.Word                      ( Word32 )
import           Data.List                      ( find )
import qualified Data.List as List
import           Data.Text.Encoding             ( encodeUtf8 )
import           Control.Monad.Reader           ( ReaderT
                                                , ask
                                                , runReaderT
                                                )
import qualified Data.Map                      as M
import qualified Data.ByteString.Lazy          as LBS

{-

-- When using the IRBuilder, both functions and variables have the type Operand
data Env = Env { operands :: M.Map Text Operand
               , structs :: [ Struct ]
               , strings :: M.Map Text Operand
               }
  deriving (Eq, Show)

-- LLVM and Codegen type synonyms allow us to emit module definitions and basic
-- block instructions at the top level without being forced to pass explicit
-- module and builder parameters to every function
type LLVM = L.ModuleBuilderT (State Env)
type Codegen = L.IRBuilderT LLVM

registerOperand :: MonadState Env m => Text -> Operand -> m ()
registerOperand name op =
  modify $ \env -> env { operands = M.insert name op (operands env) }

getFields :: MonadState Env m => Text -> m [Bind]
getFields name = do
  ss <- gets structs
  case find (\s -> structName s == name) ss of
    Nothing               -> error "Internal error - struct not found"
    Just (Struct _ binds) -> pure binds

instance ConvertibleStrings Text ShortByteString where
  convertString = fromString . T.unpack

ltypeOfTyp :: MonadState Env m => Type -> m AST.Type
ltypeOfTyp = \case
  TyVoid         -> pure AST.void
  TyInt          -> pure AST.i32
  TyChar         -> pure AST.i8
  TyFloat        -> pure AST.double
  TyBool         -> pure AST.i1
  -- (void *) is invalid LLVM
  Pointer TyVoid -> pure $ charStar
  -- special case to handle recursively defined structures
  -- TODO: add real cycle checking so that improperly defined
  -- recursive types case the compiler to hang forever
  Pointer (TyStruct n) ->
    pure $ AST.ptr (AST.NamedTypeReference (mkName $ cs ("struct." <> n)))
  Pointer  t -> fmap AST.ptr (ltypeOfTyp t)
  TyStruct n -> do
    fields <- getFields n
    typs   <- mapM (ltypeOfTyp . bindType) fields
    -- Packed structs aren't great for performance but very easy to code for now
    pure $ AST.StructureType { AST.isPacked = True, AST.elementTypes = typs }

charStar :: AST.Type
charStar = AST.ptr AST.i8

sizeof :: MonadState Env m => Type -> m Word32
sizeof = \case
  TyBool     -> pure 1
  TyChar     -> pure 1
  TyInt      -> pure 4
  TyFloat    -> pure 8
  TyVoid     -> pure 0
  Pointer  _ -> pure 8
  TyStruct n -> do
    fields <- getFields n
    sizes  <- mapM (sizeof . bindType) fields
    pure (sum sizes)

codegenLVal :: LValue -> Codegen Operand
codegenLVal (SId    name) = gets ((M.! name) . operands)
codegenLVal (SDeref e   ) = codegenSexpr e

codegenLVal (SAccess e i) = do
  e' <- codegenLVal e
  L.gep e' [L.int32 0, L.int32 (fromIntegral i)]

codegenSexpr :: SExpr -> Codegen Operand
codegenSexpr (TyInt         , SLiteral i ) = pure $ L.int32 (fromIntegral i)
codegenSexpr (TyFloat       , SFliteral f) = pure $ L.double f
codegenSexpr (TyBool        , SBoolLit b ) = pure $ L.bit (if b then 1 else 0)
codegenSexpr (TyChar        , SCharLit c ) = pure $ L.int8 (fromIntegral c)
codegenSexpr (Pointer TyChar, SStrLit s  ) = do
  -- Generate a new unique global variable for every string literal we see
  strs <- gets strings
  case M.lookup s strs of
    Nothing -> do
      let nm = mkName (show (M.size strs) <> ".str")
      op <- L.globalStringPtr (cs s) nm
      modify $ \env -> env { strings = M.insert s (AST.ConstantOperand op) strs }
      pure (AST.ConstantOperand op)
    Just op -> pure op

codegenSexpr (t    , SNull          ) = L.inttoptr (L.int64 0) =<< ltypeOfTyp t
codegenSexpr (TyInt, SSizeof t      ) = L.int32 . fromIntegral <$> sizeof t

-- All LVals are already memory addresses.
codegenSexpr (_    , SAddr e        ) = codegenLVal e
codegenSexpr (_    , LVal e         ) = flip L.load 0 =<< codegenLVal e
codegenSexpr (_    , SAssign lhs rhs) = do
  rhs' <- codegenSexpr rhs
  lhs' <- codegenLVal lhs
  L.store lhs' 0 rhs'
  return rhs'
codegenSexpr (t, SBinop op lhs rhs) = do
  lhs' <- codegenSexpr lhs
  rhs' <- codegenSexpr rhs
  case op of
    Add -> case (fst lhs, fst rhs) of
      (Pointer _, TyInt    ) -> L.gep lhs' [rhs']
      (TyInt    , Pointer _) -> L.gep rhs' [lhs']
      (TyInt    , TyInt    ) -> L.add lhs' rhs'
      (TyFloat  , TyFloat  ) -> L.fadd lhs' rhs'
      _                      -> error "Internal error - semant failed"
    Sub -> case (fst lhs, fst rhs) of
      (Pointer typ, Pointer typ') -> if typ' /= typ
        then error "Internal error - semant failed"
        else do
          lhs''  <- L.ptrtoint lhs' AST.i64
          rhs''  <- L.ptrtoint rhs' AST.i64
          diff   <- L.sub lhs'' rhs''
          width  <- L.int64 . fromIntegral <$> sizeof typ
          result <- L.sdiv diff width
          L.trunc result AST.i32
      (Pointer _, TyInt) -> do
        rhs'' <- L.sub (L.int32 0) rhs'
        L.gep lhs' [rhs'']
      (TyInt  , TyInt  ) -> L.sub lhs' rhs'
      (TyFloat, TyFloat) -> L.fsub lhs' rhs'
      _                  -> error "Internal error - semant failed"
    Mult -> case t of
      TyInt   -> L.mul lhs' rhs'
      TyFloat -> L.fmul lhs' rhs'
      _       -> error "Internal error - semant failed"
    Div -> case t of
      TyInt   -> L.sdiv lhs' rhs'
      TyFloat -> L.fdiv lhs' rhs'
      _       -> error "Internal error - semant failed"
    -- We implement int ** int directly in llvm
    Power -> mdo
      enclosing <- L.currentBlock
      L.br loop
      loop <- L.block `L.named` "loop_pow"
      acc <- L.phi [(L.int32 1, enclosing), (nextAcc, continueBlock)] `L.named` "acc"
      expt <- L.phi [(rhs', enclosing), (nextExpt, continueBlock)] `L.named` "expt"
      done <- L.icmp IP.EQ expt (L.int32 0)
      L.condBr done doneBlock continueBlock
      continueBlock <- L.block `L.named` "continue"
      nextAcc       <- L.mul acc lhs' `L.named` "next_acc"
      nextExpt      <- L.sub expt (L.int32 1) `L.named` "next_expt"
      L.br loop
      doneBlock <- L.block `L.named` "done"
      pure acc

    -- Only relational operators defined on chars, not arithmetic
    Equal -> case fst lhs of
      TyInt     -> L.icmp IP.EQ lhs' rhs'
      TyBool    -> L.icmp IP.EQ lhs' rhs'
      TyChar    -> L.icmp IP.EQ lhs' rhs'
      Pointer _ -> L.icmp IP.EQ lhs' rhs'
      TyFloat   -> L.fcmp FP.OEQ lhs' rhs'
      _         -> error "Internal error - semant failed"
    Neq -> case fst lhs of
      TyInt     -> L.icmp IP.NE lhs' rhs'
      TyBool    -> L.icmp IP.NE lhs' rhs'
      TyChar    -> L.icmp IP.NE lhs' rhs'
      Pointer _ -> L.icmp IP.NE lhs' rhs'
      TyFloat   -> L.fcmp FP.ONE lhs' rhs'
      _         -> error "Internal error - semant failed"
    Less -> case fst lhs of
      TyInt   -> L.icmp IP.SLT lhs' rhs'
      TyBool  -> L.icmp IP.SLT lhs' rhs'
      TyChar  -> L.icmp IP.ULT lhs' rhs'
      TyFloat -> L.fcmp FP.OLT lhs' rhs'
      _       -> error "Internal error - semant failed"
    Leq -> case fst lhs of
      TyInt   -> L.icmp IP.SLE lhs' rhs'
      TyBool  -> L.icmp IP.SLE lhs' rhs'
      TyChar  -> L.icmp IP.ULE lhs' rhs'
      TyFloat -> L.fcmp FP.OLE lhs' rhs'
      _       -> error "Internal error - semant failed"
    Greater -> case fst lhs of
      TyInt   -> L.icmp IP.SGT lhs' rhs'
      TyBool  -> L.icmp IP.SGT lhs' rhs'
      TyChar  -> L.icmp IP.UGT lhs' rhs'
      TyFloat -> L.fcmp FP.OGT lhs' rhs'
      _       -> error "Internal error - semant failed"
    Geq -> case fst lhs of
      TyInt   -> L.icmp IP.SGE lhs' rhs'
      TyBool  -> L.icmp IP.SGE lhs' rhs'
      TyChar  -> L.icmp IP.UGE lhs' rhs'
      TyFloat -> L.fcmp FP.OGE lhs' rhs'
      _       -> error "Internal error - semant failed"
    -- Relational operators all emit the same instructions
    -- Calling And between floats or pointers doesn't make sense,
    -- but semant catches that. Calling BitAnd between them IS allowed,
    -- and makes even less sense, but this is C, and we "trust" programmers
    -- to know why they want to do such things.
    And    -> L.and lhs' rhs'
    Or     -> L.or lhs' rhs'
    BitAnd -> L.and lhs' rhs'
    BitOr  -> L.or lhs' rhs'

codegenSexpr (t, SUnop op e) = do
  e' <- codegenSexpr e
  case op of
    Neg -> case t of
      TyInt   -> L.sub (L.int32 0) e'
      TyFloat -> L.fsub (L.double 0) e'
      _       -> error "Internal error - semant failed"
    Not -> case t of
      TyBool -> L.xor e' (L.bit 1)
      _      -> error "Internal error - semant failed"

codegenSexpr (_, SCall fun es) = do
  es' <- mapM (fmap (, []) . codegenSexpr) es
  f   <- gets ((M.! fun) . operands)
  L.call f es'

codegenSexpr (_, SCast t' e@(t, _)) = do
  e'       <- codegenSexpr e
  llvmType <- ltypeOfTyp t'
  case (t', t) of
    (Pointer _, Pointer _) -> L.bitcast e' llvmType
    (Pointer _, TyInt    ) -> L.inttoptr e' llvmType
    (TyInt    , Pointer _) -> L.ptrtoint e' llvmType
    (TyFloat  , TyInt    ) -> L.sitofp e' llvmType
    _ -> error $ "Internal error - semant failed. Invalid sexpr " <> show
      (t', SCast t e)

codegenSexpr (_, SNoexpr) = pure $ L.int64 0

-- Final catchall
codegenSexpr sx =
  error $ "Internal error - semant failed. Invalid sexpr " <> show sx


codegenStatement :: SStatement -> Codegen ()
codegenStatement (SExpr   e) = void $ codegenSexpr e

codegenStatement (SReturn e) = case e of
  (TyVoid, SNoexpr) -> L.retVoid
  _                 -> L.ret =<< codegenSexpr e

codegenStatement (SBlock ss     ) = mapM_ codegenStatement ss

codegenStatement (SIf p cons alt) = mdo
  bool <- codegenSexpr p
  L.condBr bool thenBlock elseBlock
  thenBlock <- L.block `L.named` "then"
  do
    codegenStatement cons
    mkTerminator $ L.br mergeBlock
  elseBlock <- L.block `L.named` "else"
  do
    codegenStatement alt
    mkTerminator $ L.br mergeBlock
  mergeBlock <- L.block `L.named` "merge"
  return ()

codegenStatement (SDoWhile p body) = mdo
  L.br whileBlock
  whileBlock <- L.block `L.named` "while_body"
  do
    codegenStatement body
    continue <- codegenSexpr p
    mkTerminator $ L.condBr continue whileBlock mergeBlock
  mergeBlock <- L.block `L.named` "merge"
  return ()

mkTerminator :: Codegen () -> Codegen ()
mkTerminator instr = do
  check <- L.hasTerminator
  unless check instr

-- | Generate a function and add both the function name and variable names to
-- the map.
codegenFunc :: SFunction -> LLVM ()
codegenFunc f = mdo
  -- We need to forward reference the generated function and insert it into the
  -- environment _before_ generating its body in order to handle the
  -- possibility of the function calling itself recursively
  registerOperand (sname f) function
  -- We wrap generating the function inside of the `locally` combinator in
  -- order to prevent local variables from escaping the scope of the function
  (function, strs) <- locally $ do
    retty    <- ltypeOfTyp (styp f)
    args     <- mapM mkParam (sformals f)
    fun      <- L.function name args retty genBody
    strings' <- gets strings
    pure (fun, strings')
  modify $ \e -> e { strings = strs }
 where
  name = mkName (cs $ sname f)
  mkParam (Bind t n) = (,) <$> ltypeOfTyp t <*> pure (L.ParameterName (cs n))

  -- Generate the body of the function:
  genBody :: [Operand] -> Codegen ()
  genBody ops = do
    _entry <- L.block `L.named` "entry"
    -- Add the formal parameters to the map, allocate them on the stack,
    -- and then emit the necessary store instructions
    forM_ (zip ops (sformals f)) $ \(op, Bind _ n) -> do
      addr <- L.alloca (typeOf op) Nothing 0
      L.store addr 0 op
      registerOperand n addr
    -- Same for the locals, except we do not emit the store instruction for
    -- them
    forM_ (slocals f) $ \(Bind t n) -> do
      ltype <- ltypeOfTyp t
      addr  <- L.alloca ltype Nothing 0
      registerOperand n addr
    -- Evaluate the actual body of the function after making the necessary
    -- allocations
    codegenStatement (sbody f)

emitBuiltIn :: (String, [AST.Type], AST.Type) -> LLVM ()
emitBuiltIn (name, argtys, retty) = do
  func <- L.extern (mkName name) argtys retty
  registerOperand (cs name) func

builtIns :: [(String, [AST.Type], AST.Type)]
builtIns =
  [ ("printbig"     , [AST.i32]               , AST.void)
  , ("llvm.pow.f64" , [AST.double, AST.double], AST.double)
  , ("llvm.powi.f64", [AST.double, AST.i32]   , AST.double)
  , ("malloc"       , [AST.i32]               , AST.ptr AST.i8)
  , ("free"         , [AST.ptr AST.i8]        , AST.void)
  ]

codegenGlobal :: Bind -> LLVM ()
codegenGlobal (Bind t n) = do
  typ <- ltypeOfTyp t
  let name    = mkName $ cs n
      initVal = case t of
        Pointer  _ -> C.Int 64 0
        TyStruct _ -> C.AggregateZero typ
        TyInt      -> C.Int 32 0
        TyBool     -> C.Int 1 0
        TyFloat    -> C.Float (AST.Double 0)
        TyChar     -> C.Int 8 0
        TyVoid     -> error "Global void variables illegal"
  var <- L.global name typ initVal
  registerOperand n var

emitTypeDef :: Struct -> LLVM AST.Type
emitTypeDef (Struct name _) = do
  typ <- ltypeOfTyp (TyStruct name)
  L.typedef (mkName (cs ("struct." <> name))) (Just typ)


codegenProgram :: SProgram -> AST.Module
codegenProgram (structs, globals, funcs) =
  flip evalState (Env { operands = M.empty, structs, strings = M.empty })
    $ L.buildModuleT "microc"
    $ do
        printf <- L.externVarArgs (mkName "printf") [charStar] AST.i32
        registerOperand "printf" printf
        mapM_ emitBuiltIn   builtIns
        mapM_ emitTypeDef   structs
        mapM_ codegenGlobal globals
        mapM_ codegenFunc   funcs

-}

-- Environment for tracking variables, functions, and other state during codegen
data Env = Env { 
  locals :: M.Map Text (Loc ValueType),
  funcs :: M.Map Text (Fn ()),
  structs :: [Struct],
  strings :: M.Map Text Int,
  stringData :: [(Int, LBS.ByteString)],
  nextStringOffset :: Int
} deriving (Show, Eq)

type Codegen = ReaderT Env GenFun

-- Get the WASM value type for a MicroC type
wasmType :: Type -> ValueType
wasmType TyInt = I32
wasmType TyChar = I32  -- chars are i32 in WASM
wasmType TyBool = I32  -- bools are i32 in WASM
wasmType TyFloat = F64
wasmType (Pointer _) = I32  -- pointers are i32 addresses
wasmType TyVoid = error "Cannot get WASM type for void"
wasmType (TyStruct _) = error "Structs not yet supported in WASM codegen"

-- Get size in bytes of a type
sizeOf :: Type -> Int
sizeOf TyInt = 4
sizeOf TyChar = 1
sizeOf TyBool = 1
sizeOf TyFloat = 8
sizeOf (Pointer _) = 4
sizeOf TyVoid = 0
sizeOf (TyStruct _) = error "Struct size calculation not yet implemented"

-- Code generation for expressions
codegenSexpr :: SExpr -> Codegen ()
codegenSexpr (TyInt, SLiteral i) = lift $ arg $ i32c i
codegenSexpr (TyFloat, SFliteral f) = lift $ arg $ f64c f
codegenSexpr (TyBool, SBoolLit b) = lift $ arg $ i32c (if b then 1 else 0)
codegenSexpr (TyChar, SCharLit c) = lift $ arg $ i32c (fromIntegral $ fromEnum c)
codegenSexpr (Pointer TyChar, SStrLit s) = do
    env <- ask
    let bs = LBS.fromStrict $ encodeUtf8 s
    case M.lookup s (strings env) of
        Just offset -> lift $ arg $ i32c (fromIntegral offset)
        Nothing -> error "String literal not found in environment"
codegenSexpr (_, SNull) = lift $ arg $ i32c 0
codegenSexpr (TyInt, SSizeof t) = lift $ arg $ i32c (fromIntegral $ sizeOf t)

codegenSexpr (_, LVal (SId name)) = do
    env <- ask
    case M.lookup name (locals env) of
        Just (Loc idx) -> lift $ appendExpr [GetLocal idx]
        Nothing -> error $ "Variable not found: " ++ T.unpack name

codegenSexpr (_, SAssign (SId name) rhs) = do
    env <- ask
    case M.lookup name (locals env) of
        Just (Loc idx) -> do
            codegenSexpr rhs
            lift $ appendExpr [SetLocal idx]
        Nothing -> error $ "Variable not found: " ++ T.unpack name

codegenSexpr (t, SBinop op lhs rhs) = do
    codegenSexpr lhs
    codegenSexpr rhs
    case op of
        Add -> case t of
            TyInt -> lift $ appendExpr [IBinOp BS32 IAdd]
            TyFloat -> lift $ appendExpr [FBinOp BS64 FAdd]
            _ -> error "Invalid type for Add"
        Sub -> case t of
            TyInt -> lift $ appendExpr [IBinOp BS32 ISub]
            TyFloat -> lift $ appendExpr [FBinOp BS64 FSub]
            _ -> error "Invalid type for Sub"
        Mult -> case t of
            TyInt -> lift $ appendExpr [IBinOp BS32 IMul]
            TyFloat -> lift $ appendExpr [FBinOp BS64 FMul]
            _ -> error "Invalid type for Mult"
        Div -> case t of
            TyInt -> lift $ appendExpr [IBinOp BS32 IDivS]
            TyFloat -> lift $ appendExpr [FBinOp BS64 FDiv]
            _ -> error "Invalid type for Div"
        Equal -> case fst lhs of
            TyInt -> lift $ appendExpr [IRelOp BS32 IEq]
            TyBool -> lift $ appendExpr [IRelOp BS32 IEq]
            TyChar -> lift $ appendExpr [IRelOp BS32 IEq]
            TyFloat -> lift $ appendExpr [FRelOp BS64 FEq]
            Pointer _ -> lift $ appendExpr [IRelOp BS32 IEq]
            _ -> error "Invalid type for Equal"
        Neq -> case fst lhs of
            TyInt -> lift $ appendExpr [IRelOp BS32 INe]
            TyBool -> lift $ appendExpr [IRelOp BS32 INe]
            TyChar -> lift $ appendExpr [IRelOp BS32 INe]
            TyFloat -> lift $ appendExpr [FRelOp BS64 FNe]
            Pointer _ -> lift $ appendExpr [IRelOp BS32 INe]
            _ -> error "Invalid type for Neq"
        Less -> case fst lhs of
            TyInt -> lift $ appendExpr [IRelOp BS32 ILtS]
            TyChar -> lift $ appendExpr [IRelOp BS32 ILtU]
            TyFloat -> lift $ appendExpr [FRelOp BS64 FLt]
            _ -> error "Invalid type for Less"
        Leq -> case fst lhs of
            TyInt -> lift $ appendExpr [IRelOp BS32 ILeS]
            TyChar -> lift $ appendExpr [IRelOp BS32 ILeU]
            TyFloat -> lift $ appendExpr [FRelOp BS64 FLe]
            _ -> error "Invalid type for Leq"
        Greater -> case fst lhs of
            TyInt -> lift $ appendExpr [IRelOp BS32 IGtS]
            TyChar -> lift $ appendExpr [IRelOp BS32 IGtU]
            TyFloat -> lift $ appendExpr [FRelOp BS64 FGt]
            _ -> error "Invalid type for Greater"
        Geq -> case fst lhs of
            TyInt -> lift $ appendExpr [IRelOp BS32 IGeS]
            TyChar -> lift $ appendExpr [IRelOp BS32 IGeU]
            TyFloat -> lift $ appendExpr [FRelOp BS64 FGe]
            _ -> error "Invalid type for Geq"
        And -> lift $ appendExpr [IBinOp BS32 IAnd]
        Or -> lift $ appendExpr [IBinOp BS32 IOr]
        BitAnd -> lift $ appendExpr [IBinOp BS32 IAnd]
        BitOr -> lift $ appendExpr [IBinOp BS32 IOr]
        _ -> error $ "Binary operator not yet implemented: " ++ show op

codegenSexpr (t, SUnop op e) = do
    codegenSexpr e
    case op of
        Neg -> case t of
            TyInt -> do
                lift $ appendExpr [I32Const 0]
                lift $ appendExpr [IBinOp BS32 ISub]
            TyFloat -> lift $ appendExpr [FUnOp BS64 FNeg]
            _ -> error "Invalid type for Neg"
        Not -> lift $ appendExpr [I32Eqz]

codegenSexpr (_, SCall fun es) = do
    env <- ask
    mapM_ codegenSexpr es
    case M.lookup fun (funcs env) of
        Just (Fn idx) -> lift $ appendExpr [Call idx]
        Nothing -> error $ "Function not found: " ++ T.unpack fun

codegenSexpr (_, SNoexpr) = return ()

codegenSexpr sx = error $ "Expression not yet implemented: " ++ show sx

-- Code generation for statements
codegenStatement :: SStatement -> Codegen ()
codegenStatement (SExpr e) = codegenSexpr e
codegenStatement (SReturn e) = case e of
    (TyVoid, SNoexpr) -> lift $ appendExpr [Return]
    _ -> codegenSexpr e >> lift (appendExpr [Return])
codegenStatement (SBlock ss) = mapM_ codegenStatement ss
codegenStatement _ = error "Statement not yet implemented"

-- Code generation for functions
codegenFunc :: SFunction -> GenMod (Fn ())
codegenFunc f = do
    fn <- funRec () $ \self -> do
        -- Create parameters
        paramLocs <- mapM (\(Bind t _) -> param (typeProxy t)) (sformals f)
        -- Create locals
        localLocs <- mapM (\(Bind t _) -> local (typeProxy t)) (slocals f)
        
        let paramMap = M.fromList $ zip (map (\(Bind _ n) -> n) (sformals f)) paramLocs
        let localMap = M.fromList $ zip (map (\(Bind _ n) -> n) (slocals f)) localLocs
        let allLocals = M.union paramMap localMap
        
        let env = Env {
            locals = allLocals,
            funcs = M.empty,  -- Will be filled in later
            structs = [],
            strings = M.empty,
            stringData = [],
            nextStringOffset = 0
        }
        
        runReaderT (codegenStatement (sbody f)) env
        return ()
    return fn
  where
    typeProxy :: Type -> Proxy ValueType
    typeProxy TyInt = Proxy
    typeProxy TyFloat = Proxy
    typeProxy TyBool = Proxy
    typeProxy TyChar = Proxy
    typeProxy (Pointer _) = Proxy
    typeProxy _ = error "Unsupported type"

-- Main code generation entry point
codegenProgram :: SProgram -> Module
codegenProgram (structs, globals, funcs) = genMod $ do
  -- Import memory
  mem <- importMemory "env" "memory" 1 Nothing
  
  -- Generate functions
  generatedFuncs <- mapM codegenFunc funcs
  
  -- Export main if it exists
  case List.find (\f -> sname f == "main") funcs of
      Just _ -> case List.find (\(f, sf) -> sname sf == "main") (zip generatedFuncs funcs) of
          Just (fn, _) -> export "main" fn
          Nothing -> error "no main"
      Nothing -> error "no main"
