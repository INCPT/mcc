{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module OSC.Codegen where

import Data.Functor.Identity (Identity (Identity))
import Control.Monad (when)
import Control.Monad.Fix (MonadFix)
import Control.Monad.Trans (MonadTrans, lift)
import qualified Control.Monad.Reader as R
import Control.Monad.Reader (ReaderT, asks, ask, runReaderT)
import qualified Control.Monad.State.Lazy as ST
import Control.Monad.State.Lazy (MonadState, StateT, State, state, runState, runStateT)
import Control.Monad.Trans.Writer (WriterT, runWriterT, tell)
import qualified Control.Monad.Trans.Writer as W
import Data.Functor.Product (Product (Pair))
import Data.Map (Map)
import Data.List (intercalate)
import qualified Data.Map as M
import Control.Monad.Free (Free (Free, Pure), liftF)
import qualified Control.Monad.Trans.Free as TF
import Control.Monad.Trans.Free (FreeT (FreeT), FreeF)

import OSC.Expr.Comp (Ident, Type (..), TNumber (..), Number (..), Op (..))
import qualified OSC.Expr.AnnBind as AB
import qualified OSC.Expr.Comp as C
import OSC.Expr.Functors
import OSC.Expr.Defunc

import Debug.Trace

data Location = Global Int | Local Int deriving (Eq, Ord, Show)

data Proj = PId Location | PProj Proj (Ann Type Expr)
  deriving Show

data LRef
  = LRet
  | LPushStack
  | LVar Proj
  deriving Show

projLRef :: LRef -> Ann Type Expr -> LRef
projLRef (LVar p) idx = LVar (PProj p idx)
projLRef _ _ = error "projLRef"

data RRef
  = RConst Number
  | RVar Proj
  | RPopStack
  | RFuncRef FuncRef
  deriving Show

projRRef :: RRef -> Ann Type Expr -> RRef
projRRef (RVar p) idx = RVar (PProj p idx)
projRRef _ _ = error "projLRef"

showType :: Type -> String
showType (TNumber TI32) = "i32"
showType (TNumber TF32) = "f32"
showType (TNumber TI64) = "i64"
showType (TNumber TF64) = "f64"
showType (TArr t dim) = showType t <> "[" <> show dim <> "]"
showType (TLam [] retType) = "() -> " <> showType retType
showType (TLam params retType) = 
  "(" <> intercalate ", " (map showType params) <> ") -> " <> showType retType

-- instance Show Ref where
--   show RRet = "ret"
--   show (RConst n) = show n
--   show (RVar idx) = show idx
--   show (RProj ref idx) = show ref <> "[" <> show idx <> "]"
--   show (RFuncRef (FuncRef i)) = "f" <> show i
--   show (RFuncRefRef idx) = show idx <> ":funcref"

data Slice = Slice { offset :: Int, length :: Int }
  deriving Show

sliceOf :: Int -> Int -> Slice
sliceOf = Slice

data Instruction
  = ICopy {- base type -} TNumber {- dest -} LRef Slice {- source -} RRef Slice
  | IIf RRef [Instruction] [Instruction]
  | ICall {- return ref -} LRef {- funcref -} RRef {- args -} [RRef]
  | IBinOp Op {- result -} LRef
  | IFor {- counter -} RRef {- initial -} Int {- steps -} Int {- step -} Int [Instruction]
  deriving Show

-- instance Show Instruction where
--   show (SCopy t src dst) = show dst <> " := " <> show src
--   show (SIf cond thn els) = mconcat
--     [ "if " <> show cond <> " {\n"
--     , showBlock thn
--     , "} else {\n"
--     , showBlock els
--     , "}"
--     ]
--   show (SCall funcRef args ret) = show ret <> " := " <> show funcRef <> "(" <> intercalate ", " (fmap show args) <> ")"
--   show (SBinOp op a b res) = show res <> " := " <> show a <> " " <> show op <> " " <> show b
--   show (SFor counter initial steps step body) = mconcat
--     [ "for " <> show counter <> " = " <> show initial <> " to " <> show steps <> " step " <> show step <> " {\n"
--     , showBlock body
--     , "}"
--     ]
-- 
-- showBlock :: [Instruction] -> String
-- showBlock stmts = mconcat [ "  " <> line <> "\n" | stmt <- stmts, line <- lines (show stmt) ]

-- PIPELINE --------------------------------------------------------------------

---- [] compile time constant folding (e.g. $voices etc)
---- [-] typecheck [-range propagation]
---- [] float independent computations out of rec blocks
---- [] until fixpoint
------ [] fusion/simplifications
-------- [] eval or unroll small SOACs (when unrolling compute the total number of iterations (e.g. nested SOACs can explode))
-------- [] calculate const expressions
-------- [] elim static indices [a, b, c][1] == b
-------- [] rec |...| 5.0 == 5.0
-------- [] (|a, b| a + b)(x, y) == x + y
-------- [] fuse SOACs
-------- [] ...
------ [] dead code elim
------ [] CSE (expression should hash to the same hash if e.g. bindings are reordered)
------ [] inline (awlays inline if something used only once, otherwise heuristic)
---- [] float pure expression to the topmost lambda that contains them (e.g. constant arrays will be allocated at the topmost level and become right folded selections)
---- [] float KR/AR to the topmost lambda that contains them
---- [+] ann binds
---- [+] fold selections
---- [] backend
------ [] WASM
-------- [] arrays with constants go into data sections
-------- [] simple return values on stack, arrays in linear mem
-------- [] assign array allocations
---------- [] if elems < N (8-16?) - nested ifs
---------- [] otherwise - br_table jumps
-------- [] allocate globals or locals per function (align at 4/8 bytes)
-------- [] propagate shadow stack pointers to functions that need it (e.g. if they return an array or a binding is an array or a subfunction returns an array (also transitively))

--------------------------------------------------------------------------------

data ProgramFunc = ProgramFunc
  { params :: [(Ident, Type)]
  , locals :: Map Ident Type
  , instructions :: [Instruction]
  } deriving Show

data Value = VNumber Number | VArr [Value]
  deriving Show

data Program = Program
  { globals :: Map Ident Type
  , funcMap :: Map FuncRef ProgramFunc
  , tickFunc :: ProgramFunc
  } deriving Show

type CodegenM = R.ReaderT (Map Ident Location) (W.WriterT [Instruction] (ST.State (Int, Map Location Type)))

-- innerJoin :: Applicative f => Ord k => Map k (f a) -> Map k (f b) -> Map k (f (a, b))
-- innerJoin = M.intersectionWith (\fa fb -> (,) <$> fa <*> fb)

copyRef :: TNumber -> LRef -> RRef -> CodegenM ()
copyRef typ dst src = do
  -- TODO
  -- lift $ W.tell [ICopy typ dst undefined src undefined]
  -- offsetLoc <- alloc (TNumber TI32)
  -- restDims <- calcOffset offsetLoc idxs (tail $ arrayDims bodyTyp)
  undefined
  where
    arrayDims (TArr t dim) = dim:arrayDims t
    arrayDims _ = []

    calcOffset offsetLoc [] dims = pure dims
    calcOffset offsetLoc (idx:idxs) dims@(_:dimr) = do
      -- gen LPushStack idx
      -- copyRef TI32 LPushStack (sliceOf 0 1) (RConst $ I32 $ product dims) (sliceOf 0 1)
      -- binOp Mul LPushStack
      -- copyRef TI32 LPushStack (sliceOf 0 1) (RVar offsetLoc) (sliceOf 0 1)
      -- binOp Add (LVar offsetLoc)
      calcOffset offsetLoc idxs dimr
    calcOffset _ _ [] = error "calcOffset"

binOp :: Op -> LRef -> CodegenM ()
binOp op dest = lift $ W.tell [IBinOp op dest]

call :: LRef -> RRef -> [RRef] -> CodegenM ()
call dest funcRef args = lift $ W.tell [ICall dest funcRef args]

alloc :: Type -> CodegenM Location
alloc typ = lift $ ST.state $ \(idx, m) -> (Local idx, (idx + 1, M.insert (Local idx) typ m))

if_ :: RRef -> CodegenM () -> CodegenM () -> CodegenM ()
if_ cond t e = do
  env <- R.ask
  ((), t') <- lift $ lift $ runWriterT $ runReaderT t env
  ((), e') <- lift $ lift $ runWriterT $ runReaderT e env
  lift $ W.tell [IIf cond t' e']

allocType :: Type -> CodegenM (LRef, RRef)
allocType typ = case typ of
  TNumber _ -> pure (LPushStack, RPopStack)
  TArr _ _ -> do
    loc <- alloc typ
    pure (LVar (PId loc), RVar (PId loc))
  TLam _ _ -> do
    loc <- alloc typ
    pure (LVar (PId loc), RVar (PId loc))

codegen :: DefuncMap (Ann Type) -> Ann Type Expr -> CodegenM Program
codegen dfm = undefined
  where
    collectLamAllocations :: C.LamAnn (Ann Type Expr) -> (Map Ident Type, Map Ident Type)
    collectLamAllocations (C.LamAnn typ _ bindings _) = mconcat
      [ case region of
          C.AllocLocal -> (M.singleton n t, mempty)
          C.AllocGlobal -> (mempty, M.singleton n t)
      | (n, region, Ann (t, _)) <- bindings
      ]
    
    -- TODO: do flattening of arrays and structs here; have copyVal for simple values and copySlice for array slices
    gen :: LRef -> Ann Type Expr -> CodegenM ()
    gen ret (Ann (typ, PConst n)) = copyRef (C.baseType typ) ret (RConst n)
    gen ret (Ann (typ, PVar n)) = do
      env <- R.ask
      copyRef (C.baseType typ) ret (RVar (PId (env M.! n)))
    gen ret (Ann (_, PArr elems)) = sequence_
      [ gen (projLRef ret (Ann (TNumber TI32, PConst (C.I32 i)))) elem
      | (i, elem) <- zip [0..] elems
      ]
    gen ret (Ann (_, POp op a b)) = do
      -- Values must be simple so we just push on stack (in reverse order)
      gen LPushStack b
      gen LPushStack a
      binOp op ret
    gen ret (Ann (_, (PApp (Ann (_, PFunc fr)) args))) = do
      -- Push arguments onto stack in reverse order
      rargs <- sequence
        [ do
            (larg, rarg) <- allocType atyp
            gen larg arg
            pure rarg
        | arg@(Ann (atyp, _)) <- reverse args
        ]

      call ret (RFuncRef fr) rargs
    gen ret (Ann (typ, PFunc fr)) = copyRef (C.baseType typ) ret (RFuncRef fr)
    gen ret (Ann (_, (PFoldedSelectL elems idx@(Ann (idxTyp, _))))) = do
      condLoc <- alloc (TNumber TI32)
      idxLoc <- alloc idxTyp

      gen (LVar $ PId idxLoc) idx
      recIf condLoc elems (RVar $ PId idxLoc) 0
      where
        -- TODO: binary tree if
        recIf _ [] _ _ = error "recif: no choice (this is a bug)"
        recIf _ [elem] _ _ = gen ret elem
        recIf condLoc (elem:elems) ridx i = do
          copyRef TI32 LPushStack ridx
          copyRef TI32 LPushStack (RConst (I32 i))
          binOp Eq (LVar $ PId condLoc)
          if_ (RVar $ PId condLoc) (gen ret elem) (recIf condLoc elems ridx (i + 1))
    gen ret (Ann (_, (PFoldedSelectR body@(Ann (bodyTyp, _)) idxs))) = do
      (lbody, rbody) <- allocType bodyTyp
      gen lbody body
      undefined
      where
    gen _ _ = undefined
    
{-

data Env = Env
  { bindings :: Map Ident Ref
  , ret :: Ref
  , to :: [Ref]

  , emit :: [Instruction] -> CallM ()
  , allocLocal :: Type -> CallM Ref
  }

focusTo :: Ref -> Env -> Env
focusTo idx (Env {..}) = Env { to = idx:to, .. }

data LocalState = LocalState
  { nextVarIdx :: Int
  , allocations :: [(Type, Idx)]
  }

data GlobalState = GlobalState
  { nextFuncRefIdx :: Int

  , nextGlobalVarIdx :: Int
  , globalAllocations :: [(Type, Idx)]

  , nextTickVarIdx :: Int
  , tickAllocations :: [(Type, Idx)]
  , tickInstructions :: [Instruction]
  }

type CallM = WriterT [Instruction] (ReaderT Env (StateT LocalState (State GlobalState)))

cemitLocal :: [Instruction] -> CallM ()
cemitLocal = tell

cemitGlobal :: [Instruction] -> CallM ()
cemitGlobal sts = lift $ lift $ lift $ state $ \GlobalState {..} -> ((), GlobalState { tickInstructions = tickInstructions <> sts, .. })

emit :: [Instruction] -> CallM ()
emit sts = do
  env <- lift ask
  env.emit sts

local :: Monoid w => Monad m => (env -> env) -> WriterT w (ReaderT env m) a -> WriterT w (ReaderT env m) a
local f m = do
  (a, r) <- lift $ R.local f $ runWriterT m
  tell r
  pure a

allocBase :: ((Idx -> Ref) -> m Ref) -> Type -> m Ref
allocBase alloc t = case t of
  TNumber _ -> alloc RVar
  TArr _ _ -> alloc (RArr t)
  TAbs _ _ -> alloc RFuncRefRef

callocLocal :: Type -> CallM Ref
callocLocal t = lift $ lift $ flip allocBase t $ \mkRef -> fmap mkRef $ state $ \LocalState {..} ->
  (Local nextVarIdx, LocalState { nextVarIdx = nextVarIdx + 1, allocations = (t, Local nextVarIdx):allocations, .. })

callocTick :: Type -> CallM Ref
callocTick t = lift $ lift $ lift $ flip allocBase t $ \mkRef -> fmap mkRef $ state $ \GlobalState {..} ->
  (Local nextTickVarIdx, GlobalState { nextTickVarIdx = nextTickVarIdx + 1, tickAllocations = (t, Local nextTickVarIdx):tickAllocations, .. })

allocLocal :: Type -> CallM Ref
allocLocal t = do
  env <- lift ask
  env.allocLocal t

allocGlobal :: Type -> State GlobalState Ref
allocGlobal t = flip allocBase t $ \mkRef -> fmap mkRef $ state $ \GlobalState {..} ->
  (Global nextGlobalVarIdx, GlobalState { nextGlobalVarIdx = nextGlobalVarIdx + 1, globalAllocations = (t, Global nextGlobalVarIdx):globalAllocations, .. })

--------------------------------------------------------------------------------

cextract :: Monoid w => Monad m => WriterT w (ReaderT env m) () -> ReaderT env m w
cextract = fmap snd . runWriterT

ccopyRef :: Type -> Ref -> Ref -> CallM ()
ccopyRef t src dst = emit [SCopy t src dst]

cbinOp :: Op -> Ref -> Ref -> Ref -> CallM ()
cbinOp op r1 r2 r3 = emit [SBinOp op r1 r2 r3]

ccall :: Ref -> [Ref] -> Ref -> CallM ()
ccall funcRef args ret = emit [SCall funcRef args ret]

cif :: Ref -> CallM () -> CallM () -> CallM ()
cif r t e = do
  t' <- lift $ cextract t
  e' <- lift $ cextract e
  emit [SIf r t' e']

cfor :: Int -> Int -> Int -> (Ref -> CallM ()) -> CallM ()
cfor initial steps step f = do
  i <- allocLocal (TNumber TI32)
  f' <- lift $ cextract (f i)
  emit [SFor i initial steps step f']

--------------------------------------------------------------------------------

allocAndStore :: AllocRegion -> CExpr FuncRef -> CallM (Type, Ref)
allocAndStore region e = do
  ref <- case region of
    ALocal -> allocLocal t
    AGlobal -> lift $ lift $ lift $ allocGlobal t
  local (\Env {..} -> Env { ret = ref, to = [], .. }) (retvalue e)
  pure (t, ref)
  where
    t = cexprType e

proj :: Ref -> [Ref] -> Ref
proj ref [] = ref
proj ref (pj:pjs) = RProj (proj ref pjs) pj

ret :: Type -> Ref -> CallM ()
ret t ref = do
  env <- ask
  ccopyRef t ref (proj env.ret (reverse env.to))

--------------------------------------------------------------------------------

rhsvalue :: AllocRegion -> CExpr FuncRef -> CallM (Type, Ref)

rhsvalue _ (CConst n) = pure (numberType n, RConst n)
rhsvalue _ (CAbs t fr) = pure (t, RFuncRef fr)
rhsvalue region e@(CArr _ _) = allocAndStore region e
rhsvalue region e@(COp _ _ _ _) = allocAndStore region e
rhsvalue region e@(CSel _ _ _) = allocAndStore region e

-- Indexed expressions
rhsvalue _ (CIndexed [] (CVar t n)) = do
  env <- ask
  case M.lookup n env.bindings of
    Just ref -> pure (t, ref)
    _ -> error $ "rhsvalue: unknown global (this is a bug): " <> show n <> ", " <> show env.bindings
rhsvalue region e@(CIndexed _ _) = allocAndStore region e

--------------------------------------------------------------------------------

retvalue :: CExpr FuncRef -> CallM ()

retvalue (CConst c) = ret (numberType c) (RConst c)
retvalue (CAbs t fr) = ret t (RFuncRef fr)
retvalue (CArr _ elems) = sequence_
  [ local (focusTo $ RConst $ I32 i) $ retvalue elem
  | (i, elem) <- zip [0..] elems
  ]
retvalue (COp _ op a b) = do
  (_, aref) <- rhsvalue ALocal a
  (_, bref) <- rhsvalue ALocal b
  
  ask >>= \env -> cbinOp op aref bref env.ret

retvalue e@(CIndexed [] (CVar _ _)) = rhsvalue ALocal e >>= uncurry ret

retvalue (CIndexed [] (CApp _ f as)) = do
  (_, fref) <- rhsvalue ALocal f
  arefs <- traverse (rhsvalue ALocal) as
    
  ask >>= \env -> ccall fref (map snd arefs) env.ret

retvalue (CIndexed [] (CRec t delay param bindings body))
  | typeContainsAbs t = error "retvalue: CRec: type contains abstraction"
  | otherwise = do
      -- Alloc delay index and delay number of samples of type t[]
      delayRef <- lift $ lift $ lift $ allocGlobal (TArr t delay)

      writeIdx <- lift $ lift $ lift $ allocGlobal (TNumber TI32)
      ccopyRef (TNumber TI32) (RConst (I32 (delay - 1))) writeIdx

      readIdx <- lift $ lift $ lift $ allocGlobal (TNumber TI32)
      ccopyRef (TNumber TI32) (RConst (I32 0)) readIdx

      -- Emit global tick instructions and store result in delay line
      local (\Env {..} -> Env { emit = cemitGlobal, allocLocal = callocTick, ret = proj delayRef [writeIdx], .. }) $ mdo
        bindingRefs <- mconcat <$> sequenceA
          [ pure $ M.singleton param (proj delayRef [readIdx])
          , M.fromList <$> sequenceA [ (n,) . snd <$> local withBindingRefs (rhsvalue region bbody) | (n, region, bbody) <- bindings ]
          ]

        let withBindingRefs :: Env -> Env
            withBindingRefs Env {..} = Env { bindings = bindingRefs <> bindings, .. }

        local withBindingRefs $ retvalue body

        -- Increment read & write index
        cbinOp Add writeIdx (RConst $ I32 1) writeIdx
        cbinOp Mod writeIdx (RConst $ I32 delay) writeIdx
      
        -- TODO: variable delay
        cbinOp Add readIdx (RConst $ I32 1) readIdx
        cbinOp Mod readIdx (RConst $ I32 delay) readIdx

      -- Copy result from delay line
      ret t $ proj delayRef [writeIdx]
  where
    typeContainsAbs (TNumber _) = False
    typeContainsAbs (TArr t _) = typeContainsAbs t
    typeContainsAbs (TAbs _ _) = True

-- General indexed expression
retvalue (CIndexed idxs indexable) = do
  idxRefs <- sequence [ rhsvalue ALocal idx | (_, idx) <- idxs ]
  (t, ref) <- rhsvalue ALocal (CIndexed [] indexable)
  ret t $ proj ref (fmap snd idxRefs)

retvalue (CSel _ chs sel) = do
  (_, sref) <- rhsvalue ALocal sel
  cond <- allocLocal (TNumber TI32)
  recif cond chs sref 0
  where
    -- TODO: binary tree if
    recif _ [] _ _ = error "recif: no choice (this is a bug)"
    recif _ [ch] _ _ = retvalue ch
    recif cond (ch:chs) sref idx = do
      cbinOp Eq sref (RConst (I32 idx)) cond
      cif cond (retvalue ch) (recif cond chs sref (idx + 1))

--------------------------------------------------------------------------------

data IRFunc = IRFunc
  { allocations :: [(Type, Idx)]
  , instructions :: [Instruction]
  } deriving Show

data IR = IR
  { globalAllocations :: [(Type, Idx)]
  , funcMap :: Map FuncRef IRFunc
  , tickFunc :: IRFunc
  } deriving Show

toplevel :: Map Ident Type -> Map FuncRef Func -> IR
toplevel globals funcRefMap = IR
  { globalAllocations = st.globalAllocations
  , tickFunc = IRFunc
      { allocations = st.tickAllocations
      , instructions = st.tickInstructions
      }
  , .. }
  where
    (funcMap, st) = runState gen $ GlobalState
      { nextFuncRefIdx = 0
      , nextGlobalVarIdx = 0
      , globalAllocations = []
      , nextTickVarIdx = 0
      , tickAllocations = []
      , tickInstructions = []
      }

    gen :: State GlobalState (Map FuncRef IRFunc)
    gen = do
      globalRefs <- M.fromList <$> sequence [ (n,) <$> allocGlobal t | (n, t) <- M.toList globals ]

      M.fromList <$> sequence
        [ do
           (((), instructions), lst) <-
               flip runStateT (LocalState { nextVarIdx = 0, allocations = [] })
             $ flip runReaderT (Env { bindings = globalRefs, ret = RRet, to = [], emit = cemitLocal, allocLocal = callocLocal })
             $ runWriterT
             $ func f
           pure (fr, IRFunc { allocations = lst.allocations, .. })
        | (fr, f) <- M.toList funcRefMap
        ]

      where
        func (Func _ params bindings body) = mdo
          bindingRefs <- mconcat <$> sequenceA
            -- Arguments
            [ pure $ M.fromList [ (p, RArg idx) | (idx, p) <- zip [0..] params ]

            -- Bindings (must be in topsort order)
            , M.fromList <$> sequenceA
                [ case region of
                    ALocal -> (n,) . snd <$> local withBindingRefs (rhsvalue region bbody)
                    AGlobal -> do
                      -- Set global ref as return value for binding rhs
                      gref <- asks ((M.! n) . (.bindings))
                      local ((\Env {..} -> Env { ret = gref, .. }) . withBindingRefs) (retvalue bbody)
                      pure (n, gref)
                | (n, region, bbody) <- bindings
                ]
            ]

          let withBindingRefs :: Env -> Env
              withBindingRefs Env {..} = Env { bindings = bindingRefs <> bindings, .. }

          local withBindingRefs $ retvalue body

-}

-- TODO: dead code elimination
-- TODO: array interval OOB detection

-- RJCT: topsort global instructions

-- DONE: no toplevel definitions, everything is a function
-- DONE: topsort bindings when generating a function

-- TODO: HM type inference -> lambda specialization -> inline -> CSE -> float pure expressions out of CSel/etc

-- TODO: use mtl constraints for allocLocal/Global?
-- TODO: use lhs/rhs for clarity

-- TODO: oversampling just means that we insert some stateful code around the oversampled function (which we should always inline when generating code; this can happen directly in the codegen)
-- TODO: zig std math: https://github.com/ziglang/zig/tree/master/lib/std/math

-- NOTE: selection only happens after "opaque" transitions, e.g. function call or global ref; an array paired with a selection is a choice
-- DONE: local var indices should be function local?
--- https://github.com/juce-framework/JUCE/blob/master/modules/juce_dsp/processors/juce_Oversampling.cpp
-- DONE: can't return Abs from Rec
-- DONE: generate SAbs code; pretty straightforward
-- DONE: replace refs to params with RArg 0, 1, 2 etc
-- RJCT: rec and oversample take a lambda abstraction (or a Var pointing to a lambda abstraction)