{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TupleSections #-}

module OSC.Call where

import Data.Functor.Identity (Identity (Identity))
import Control.Monad (when)
import Control.Monad.Fix (MonadFix)
import Control.Monad.Trans (MonadTrans, lift)
import qualified Control.Monad.Reader as R
import qualified Control.Monad.State as ST
import qualified Control.Monad.Trans.Writer.CPS as W
import Data.Functor.Product (Product (Pair))
import Data.Map (Map)
import qualified Data.Map as M
import Control.Monad.Free (Free (Free, Pure), liftF)
import qualified Control.Monad.Trans.Free as TF
import Control.Monad.Trans.Free (FreeT (FreeT), FreeF)
import OSC.Ctx

data Idx = Local Int | Global Int deriving (Eq, Ord, Show)

data Ref 
  = RArg Int
  | RConst Number

  | RVar Idx -- either a function local var index (e.g. in function f() { int a; float b; } would be locals with index 0 and 1) or an index into a global var table

  | RArr Type Idx -- global base address of array in a linear memory layout
  | RProj {- ref must be an array -} Ref [Ref] -- projection from or into array

  | RFuncRef FuncRef -- index into a global function table
  | RFuncRefRef Idx -- local or global var index with index into global function table (e.g. pointer to a function pointer)
  deriving Show

--------------------------------------------------------------------------------

-- INFORMAL SPECS

-- the calling convention is: simple values and references on the stack + a reference to where the result must be placed; the caller allocates the destination

-- for example when the function(x: i32, y: i32): i32[2][2] { return [[x, y], f(x + y)] } is called:
--   the caller allocates a flat i32 array with 2 * 2 elements
--   puts x and y on stack, calls function
--   when an array is returned we traverse each element and add its index into lens.to
--     the nested array traverses in turn ints elements and adds each one to lens.to
--       for example when coming to 'y' we'd be in the first element of the outer array and the second element of the inner (i.e. lens.to = [0, 1])
--       since 'y' is a value and can't be evaluated further we copy it using CopyConst or CopyRef to the destination slice (lens.to)
--     when calling f(x + y) its return value reference is computed as current_ret_reference + offset of element [0][1] into flat return array
--       this means essentially zero copying of data
--  on the other hand if we return a selection (e.g. f()[x][y]) (so f() is higher dimensional than the return type of the current function)
--    then space for the return value ret_val of f() is allocated, f called and a CopyRef operation (reference to ret_val, lens.from = [x][y]) => (current_ret_reference, lens.to = [...]) performed

-- NOTE: a literal array paired with a selection is a choice

data Lens = Lens { from :: [Ref], to :: [Ref] }
  deriving Show

data Env = Env
  { globals :: Map Ident Ref
  , ret :: Ref
  , to :: [Ref]
  }

focusTo :: Ref -> Env -> Env
focusTo idx (Env {..}) = Env { to = to <> [idx], .. }

--------------------------------------------------------------------------------

data Statement
  = SCopy Type Ref Ref
  | SIf Ref [Statement] [Statement]
  | SCall Ref [Ref] Ref
  | SBinOp Op Ref Ref Ref
  | SFor {- counter -} Ref {- initial -} Int {- steps -} Int {- step -} Int [Statement]
  deriving Show

data Allocation = Allocation Type Idx

data AllocState = AllocState
  { localIdx :: Int
  , globalIdx :: Int
  , allocations :: [Allocation]
  , funcRefIdx :: Int
  }

type CallM = R.ReaderT Env (W.WriterT [Statement] (ST.State AllocState))

cextract :: CallM () -> CallM [Statement]
cextract m = do
  env <- R.ask
  fmap snd $ lift $ lift $ W.runWriterT (R.runReaderT m env)

calloc :: Type -> AllocRegion -> CallM Ref
calloc t region = case t of
  TNumber _ -> fmap RVar $ lift $ lift (allocInRegion region)
  TArr _ _-> fmap (RArr t) $ lift $ lift (allocInRegion region)
  TAbs _ _ -> fmap RFuncRefRef $ lift $ lift (allocInRegion region)
  where
    allocInRegion :: AllocRegion -> ST.State AllocState Idx
    allocInRegion AGlobal = ST.state $ \st -> (Global st.globalIdx, st { globalIdx = st.globalIdx + 1, allocations = Allocation t (Global st.globalIdx):st.allocations})
    allocInRegion ALocal = ST.state $ \st -> (Local st.localIdx, st { localIdx = st.localIdx + 1, allocations = Allocation t (Local st.localIdx):st.allocations})

ccopyRef :: Type -> Ref -> Ref -> CallM ()
ccopyRef t src dst = lift $ W.tell [SCopy t src dst]

cbinOp :: Op -> Ref -> Ref -> Ref -> CallM ()
cbinOp op r1 r2 r3 = lift $ W.tell [SBinOp op r1 r2 r3]

ccall :: Ref -> [Ref] -> Ref -> CallM ()
ccall funcRef args ret = lift $ W.tell $ [SCall funcRef args ret]

cif :: Ref -> CallM () -> CallM () -> CallM ()
cif r t e = do
  t' <- cextract t
  e' <- cextract e
  lift $ W.tell [SIf r t' e']

cfor :: Int -> Int -> Int -> (Ref -> CallM ()) -> CallM ()
cfor initial steps step f = do
  i <- calloc (TNumber TI32) ALocal
  f' <- cextract (f i)
  lift $ W.tell [SFor i initial steps step f']

--------------------------------------------------------------------------------

allocGlobals :: Map Ident Type -> CallM (Map Ident Ref)
allocGlobals = traverse (\t -> calloc t AGlobal)

allocAndStore :: AllocRegion -> CExpr FuncRef -> CallM (Type, Ref)
allocAndStore region e = do
  ref <- calloc t region
  R.local (\Env {..} -> Env { ret = ref, to = [], .. }) (retvalue e)
  pure (t, ref)
  where
    t = cexprType e

ret :: Type -> Ref -> CallM ()
ret t ref = do
  env <- R.ask
  ccopyRef t ref (RProj env.ret env.to)

--------------------------------------------------------------------------------

rhsvalue :: AllocRegion -> CExpr FuncRef -> CallM (Type, Ref)

rhsvalue _ (CConst n) = pure (numberType n, RConst n)
rhsvalue _ (CAbs t fr) = pure (t, RFuncRef fr)
rhsvalue region e@(CArr _ _) = allocAndStore region e
rhsvalue region e@(COp _ _ _ _) = allocAndStore region e
rhsvalue region e@(CSel _ _ _) = allocAndStore region e

-- Indexed expressions
rhsvalue _ (CIndexed [] (CVar t n)) = do
  env <- R.ask
  case M.lookup n env.globals of
    Just ref -> pure (t, ref)
    _ -> error "rhsvalue: unknown global (this is a bug)"
rhsvalue region e@(CIndexed _ _) = allocAndStore region e

--------------------------------------------------------------------------------

retvalue :: CExpr FuncRef -> CallM ()

retvalue (CConst c) = ret (numberType c) (RConst c)
retvalue (CAbs t fr) = ret t (RFuncRef fr)
retvalue (CArr _ elems) = sequence_
  [ R.local (focusTo $ RConst $ I32 i) $ retvalue elem
  | (i, elem) <- zip [0..] elems
  ]
retvalue (COp _ op a b) = do
  (_, aref) <- rhsvalue ALocal a
  (_, bref) <- rhsvalue ALocal b
  
  R.ask >>= \env -> cbinOp op aref bref env.ret

retvalue e@(CIndexed [] (CVar _ _)) = rhsvalue ALocal e >>= uncurry ret

retvalue (CIndexed [] (CApp _ f as)) = do
  (_, fref) <- rhsvalue ALocal f
  arefs <- traverse (rhsvalue ALocal) as
    
  R.ask >>= \env -> ccall fref (map snd arefs) env.ret

retvalue (CIndexed [] (CRec t delay param bindings body))
  | typeContainsAbs t = error "retvalue: CRec: type contains abstraction"
  | otherwise = mdo
      -- Alloc delay number of samples of type t[]
      delayRef <- calloc (TArr t delay) AGlobal
      delayIdx <- calloc (TNumber TI32) AGlobal

      bindingRefs <- mconcat <$> sequence
        [ pure $ M.singleton param (RProj delayRef [delayIdx])
        , M.fromList <$> sequenceA [ (n,) <$> R.local withBindingRefs (snd <$> rhsvalue region bbody) | (n, region, bbody) <- bindings ]
        ]

      let withBindingRefs :: Env -> Env
          withBindingRefs Env {..} = Env { globals = bindingRefs <> globals, .. }

      R.local withBindingRefs $ retvalue body
      
      -- Copy result to delay line
      R.ask >>= \env -> ccopyRef t env.ret (RProj delayRef [delayIdx])

      cbinOp Add delayRef (RConst $ I32 1) delayRef
      cbinOp Mod delayRef (RConst $ I32 delay) delayRef
  where
    typeContainsAbs (TNumber _) = False
    typeContainsAbs (TArr t _) = typeContainsAbs t
    typeContainsAbs (TAbs _ _) = True

-- General indexed expression
retvalue (CIndexed idxs indexable) = do
  idxRefs <- sequence [ rhsvalue ALocal idx | (_, idx) <- idxs ]
  (t, ref) <- rhsvalue ALocal (CIndexed [] indexable)
  ret t $ RProj ref (fmap snd idxRefs)

retvalue (CSel _ chs sel) = do
  env <- R.ask

  (_, sref) <- rhsvalue ALocal sel
  recif env chs sref 0
  where
    -- TODO: binary tree if
    recif _ [] _ _ = error "recif: no choice (this is a bug)"
    recif _ [ch] _ _ = retvalue ch
    recif env (ch:chs) sref idx = do
      cond <- calloc (TNumber TI32) ALocal
      cbinOp Eq sref (RConst (I32 idx)) cond

      cif cond (retvalue ch) (recif env chs sref (idx + 1))

toplevel :: M.Map Ident (CExpr FuncRef) -> Map FuncRef Func -> CallM (Map FuncRef Ref)
toplevel m funcRefMap = M.fromList <$> sequence [ (n,) <$> go n f | (n, f) <- M.toList funcRefMap ]
  where
    go n (Func _ params bindings body) = mdo
      bindingRefs <- mconcat <$> sequence
        [ pure $ M.fromList [ (p, RArg idx) | (idx, p) <- zip [0..] params ]
        , M.fromList <$> sequenceA [ (n,) <$> R.local withBindingRefs (snd <$> rhsvalue region bbody) | (n, region, bbody) <- bindings ]
        ]
      let withBindingRefs :: Env -> Env
          withBindingRefs Env {..} = Env { globals = bindingRefs <> globals, .. }

      R.local withBindingRefs $ snd <$> rhsvalue AGlobal body

-- TODO: oversampling just means that we insert some stateful code around the oversampled function (which we should always inline when generating code; this can happen directly in the codegen)
--- https://github.com/juce-framework/JUCE/blob/master/modules/juce_dsp/processors/juce_Oversampling.cpp
-- TODO: can't return Abs from Rec
-- NOTE: selection only happens after "opaque" transitions, e.g. function call or global ref; an array paired with a selection is a choice
-- TODO: generate SAbs code; pretty straightforward
-- TODO: replace refs to params with RArg 0, 1, 2 etc
-- TODO: rec and oversample take a lambda abstraction (or a Var pointing to a lambda abstraction)
-- TODO: zig std math: https://github.com/ziglang/zig/tree/master/lib/std/math
