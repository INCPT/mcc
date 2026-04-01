{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE OverloadedRecordDot #-}
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
  | RArray Type Idx -- global base address of array in a linear memory layout
  | RFuncRef FuncRef -- index into a global function table

  -- double references
  | RRArray Type Idx -- contains the local/global var index containing the base address of an array
  | RRFuncRef Idx -- contains the local/global var index containing the index into the function table
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

data Lens = Lens { from :: [Ref], to :: [Int] }

data Env = Env
  { typ :: Type
  , ret :: Ref
  , lens :: Lens
  }

newEnv :: Type -> Ref -> Env
newEnv t ref = Env t ref (Lens [] [])

focusTo :: Int -> Env -> Env
focusTo idx env = env { lens = env.lens { to = env.lens.to <> [idx] } }

focusFrom :: [Ref] -> Env -> Env
focusFrom idxs env = env { lens = env.lens { from = env.lens.from <> idxs } }

data IRF n
  = Ref Ref

  | Alloc Type AllocRegion (Ref -> n)

  -- copies the value referenced by the first Ref into the second Ref respecting both lens.from and lens.to
  -- the N-D (N dimensional) lens describes two N-D subslices of an M-D source tensor to a a K-D destination tensor (N >= 1, M >= N, K >= N)
  | CopyRef Type Ref Ref Lens

  | BinOp Op Ref Ref Ref

  | If Ref (IR ()) (IR ())

  | Call Ref [Ref] Ref -- first Ref must be an RFuncRef or an RRFuncRef; then arguments; then destination
  deriving Functor

type IR = Free IRF

copyRef :: Type -> Ref -> Ref -> Lens -> IR ()
copyRef t src dst lens = liftF $ CopyRef t src dst lens

binOp :: Op -> Ref -> Ref -> Ref -> IR ()
binOp op r1 r2 r3 = liftF $ BinOp op r1 r2 r3

call :: Ref -> [Ref] -> Ref -> IR ()
call funcRef args ret = liftF $ Call funcRef args ret

alloc :: Type -> AllocRegion -> IR Ref
alloc t region = liftF $ Alloc t region id

ref :: Ref -> IR Ref
ref r = pure r

_if :: Ref -> IR () -> IR () -> IR ()
_if r t e = liftF $ If r t e

--------------------------------------------------------------------------------

data Statement
  = SCopy Type Ref Ref Lens
  | SIf Ref [Statement] [Statement]
  | SCall Ref [Ref] Ref
  | SBinOp Op Ref Ref Ref
  | SFor {- counter -} Ref {- initial -} Int {- steps -} Int {- step -} Int [Statement]

data Allocation = Allocation Type Idx

data AllocState = AllocState
  { localIdx :: Int
  , globalIdx :: Int
  , allocations :: [Allocation]
  }

type CallM = R.ReaderT Env (W.WriterT [Statement] (ST.State AllocState))

cextract :: CallM () -> CallM [Statement]
cextract m = do
  env <- R.ask
  fmap snd $ lift $ lift $ W.runWriterT (R.runReaderT m env)

calloc :: Type -> AllocRegion -> CallM Ref
calloc t region = case t of
  TArr _ _-> fmap (RArray t) $ lift $ lift (allocInRegion region)
  TI32 -> fmap RVar $ lift $ lift (allocInRegion region)
  TF32 -> fmap RVar $ lift $ lift (allocInRegion region)
  TI64 -> fmap RVar $ lift $ lift (allocInRegion region)
  TF64 -> fmap RVar $ lift $ lift (allocInRegion region)
  TAbs _ _ -> error "alloc: SAbs (this is a bug)"
  where
    allocInRegion :: AllocRegion -> ST.State AllocState Idx
    allocInRegion AGlobal = ST.state $ \st -> (Global st.globalIdx, st { globalIdx = st.globalIdx + 1, allocations = Allocation t (Global st.globalIdx):st.allocations})
    allocInRegion ALocal = ST.state $ \st -> (Local st.localIdx, st { localIdx = st.localIdx + 1, allocations = Allocation t (Local st.localIdx):st.allocations})

ccopyRef :: Type -> Ref -> Ref -> Lens -> CallM ()
ccopyRef t src dst lens = lift $ W.tell [SCopy t src dst lens]

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
  i <- calloc TI32 ALocal
  f' <- cextract (f i)
  lift $ W.tell [SFor i initial steps step f']

--------------------------------------------------------------------------------

allocGlobals :: Map Ident Type -> IR (Map Ident Ref)
allocGlobals = traverse $ \t -> alloc t AGlobal

allocAndStore :: Map Ident Ref -> Type -> Choice -> CallM Ref
allocAndStore globals t e = do
  ref <- calloc t ALocal
  R.local (const $ newEnv t ref) (sexpr globals e)
  pure ref

ret :: Type -> Ref -> CallM ()
ret t ref = do
  env <- R.ask
  ccopyRef t ref env.ret env.lens

rvalue :: Map Ident Ref -> Choice -> CallM (Type, Ref)
rvalue _ (CExpr _ (SConst n)) = pure (numberType n, RConst n)
rvalue _ (CExpr _ (SFuncRef t fr)) = pure (t, RFuncRef fr)
rvalue globals (CExpr _ (SVar t n))
  | Just ref <- M.lookup n globals = pure (t, ref)
  | otherwise = error "rvalue: unknown global (this is a bug)"
rvalue globals (CExpr _ (SVarNS t n))
  | Just ref <- M.lookup n globals = pure (t, ref)
  | otherwise = error "rvalue: unknown global (this is a bug)"
rvalue globals e@(CExpr _ (SArr t _)) = (t,) <$> allocAndStore globals t e
rvalue _ (CExpr _ (SAbs _ _ _)) = error "rvalue: SAbs: (this is a bug)"
rvalue globals e@(CExpr _ (SApp t _ _)) = (t,) <$> allocAndStore globals t e

rvalue _ _ = undefined

sexpr :: Map Ident Ref -> Choice -> CallM ()
sexpr globals e@(CExpr [] (SConst _)) = rvalue globals e >>= uncurry ret
sexpr globals e@(CExpr [] (SFuncRef _ _)) = rvalue globals e >>= uncurry ret
sexpr globals e@(CExpr [] (SVar _ _)) = rvalue globals e >>= uncurry ret
sexpr globals e@(CExpr [] (SVarNS _ _)) = rvalue globals e >>= uncurry ret
sexpr globals (CExpr [] (SArr _ elems)) = sequence_
  [ R.local (focusTo i) $ sexpr globals elem
  | (i, elem) <- zip [0..] elems
  ]
sexpr _ (CExpr _ (SArr _ _)) = error "sexpr: SArr: non empty selection indices (this is a bug)"
sexpr globals (CExpr [] (SOp _ op a b)) = do
  (_, aref) <- rvalue globals a
  (_, bref) <- rvalue globals b
  
  R.ask >>= \env -> cbinOp op aref bref env.ret

sexpr _ (CExpr _ (SOp _ _ _ _)) = error "sexpr: SOp: non empty selection indices (this is a bug)"
sexpr _ (CExpr _ (SAbs _ _ _)) = error "sexpr: SAbs: (this is a bug)"

sexpr globals (CExpr _ (SApp _ f as)) = do -- TODO: sel indices
  (_, fref) <- rvalue globals f
  arefs <- traverse (rvalue globals) as
    
  R.ask >>= \env -> ccall fref (map snd arefs) env.ret

-- General selection expression
sexpr globals (CExpr idxs cexpr) = do
  refs <- sequence [ rvalue globals idx | (_, idx) <- idxs ]
  R.local (focusFrom $ fmap snd refs) (sexpr globals (CExpr [] cexpr))

sexpr globals (CChoice _ chs sel) = do
  env <- R.ask

  (_, sref) <- rvalue globals sel
  recif env chs sref 0
  where
    -- TODO: binary tree if
    recif _ [] _ _ = error "recif: no choice (this is a bug)"
    recif _ [ch] _ _ = sexpr globals ch
    recif env (ch:chs) sref idx = do
      cond <- calloc TI32 ALocal
      cbinOp Eq sref (RConst (I32 idx)) cond

      cif cond (sexpr globals ch) (recif env chs sref (idx + 1))

-- TODO
sexpr globals (CRec t delay n ini body) = sexpr globals body

-- TODO: oversampling just means that we insert some stateful code around the oversampled function (which we should always inline when generating code; this can happen directly in the codegen)
--- https://github.com/juce-framework/JUCE/blob/master/modules/juce_dsp/processors/juce_Oversampling.cpp
-- TODO: can't return Abs from Rec
-- TODO: all local allocations upfront
-- NOTE: selection only happens after "opaque" transitions, e.g. function call or global ref; an array paired with a selection is a choice
-- TODO: generate SAbs code; pretty straightforward
-- TODO: replace refs to params with RArg 0, 1, 2 etc
-- TODO: rec and oversample take a lambda abstraction (or a Var pointing to a lambda abstraction)
-- TODO: zig std math: https://github.com/ziglang/zig/tree/master/lib/std/math
abs :: Map Ident Ref -> Abs -> CallM Ref
abs = undefined
