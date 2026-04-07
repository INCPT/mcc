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
  | RProj {- source/dest -} Ref {- index -} Ref -- projection from or into array

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

data Env = Env
  { bindings :: Map Ident Ref
  , ret :: Ref
  , to :: [Ref]
  , localIdx :: Int
  , allocations :: [(Type, Idx)]
  }

focusTo :: Ref -> Env -> Env
focusTo idx (Env {..}) = Env { to = idx:to, .. }

--------------------------------------------------------------------------------

data Statement
  = SCopy Type {- source -} Ref {- dest -} Ref
  | SIf Ref [Statement] [Statement]
  | SCall {- funcref -} Ref {- args -} [Ref] {- return ref -} Ref
  | SBinOp Op {- a -} Ref {- b -} Ref {- result -} Ref
  | SFor {- counter -} Ref {- initial -} Int {- steps -} Int {- step -} Int [Statement]
  deriving Show

data Allocation = Allocation Type Idx

data AllocState = AllocState
  { globalIdx :: Int
  , allocations :: [(Type, Idx)]
  , funcRefIdx :: Int
  }

type CallMBase = W.WriterT [Statement] (ST.State AllocState)
type CallM = R.ReaderT Env CallMBase

cextract :: CallM () -> CallM [Statement]
cextract m = do
  env <- R.ask
  fmap snd $ lift $ lift $ W.runWriterT (R.runReaderT m env)

allocLocal :: Type -> (Ref -> CallM a) -> CallM a
allocLocal t k = case t of
  TNumber _ -> alloc RVar
  TArr _ _ -> alloc (RArr t)
  TAbs _ _ -> alloc RFuncRefRef
  where
    alloc mkRef = do
      env <- R.ask
      R.local (\Env {..} -> Env { localIdx = localIdx + 1, allocations = (t, Local localIdx):allocations, .. }) $ k (mkRef $ Local env.localIdx)

allocGlobal :: Type -> CallMBase Ref
allocGlobal t = lift $ case t of
  TNumber _ -> alloc RVar
  TArr _ _ -> alloc (RArr t)
  TAbs _ _ -> alloc RFuncRefRef
  where
    alloc :: (Idx -> Ref) -> ST.State AllocState Ref
    alloc mkRef = fmap mkRef $ ST.state $ \AllocState {..} ->
      (Global globalIdx, AllocState { globalIdx = globalIdx + 1, allocations = (t, Global globalIdx):allocations, .. })

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
cfor initial steps step f = allocLocal (TNumber TI32) $ \i -> do
  f' <- cextract (f i)
  lift $ W.tell [SFor i initial steps step f']

--------------------------------------------------------------------------------

allocAndStore :: AllocRegion -> CExpr FuncRef -> CallM (Type, Ref)
allocAndStore ALocal e = allocLocal t $ \ref -> do
  R.local (\Env {..} -> Env { ret = ref, to = [], .. }) (retvalue e)
  pure (t, ref)
  where
    t = cexprType e
allocAndStore AGlobal e = do
  ref <- lift $ allocGlobal t
  R.local (\Env {..} -> Env { ret = ref, to = [], .. }) (retvalue e)
  pure (t, ref)
  where
    t = cexprType e

proj :: Ref -> [Ref] -> Ref
proj ref [] = ref
proj ref (pj:pjs) = RProj (proj ref pjs) pj

ret :: Type -> Ref -> CallM ()
ret t ref = do
  env <- R.ask
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
  env <- R.ask
  case M.lookup n env.bindings of
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
      delayRef <- lift $ allocGlobal (TArr t delay)
      delayIdx <- lift $ allocGlobal (TNumber TI32)

      bindingRefs <- mconcat <$> sequenceA
        [ pure $ M.singleton param (proj delayRef [delayIdx])
        , M.fromList <$> sequenceA [ (n,) . snd <$> R.local withBindingRefs (rhsvalue region bbody) | (n, region, bbody) <- bindings ]
        ]

      let withBindingRefs :: Env -> Env
          withBindingRefs Env {..} = Env { bindings = bindingRefs <> bindings, .. }

      R.local withBindingRefs $ retvalue body
      
      -- Copy result to delay line
      R.ask >>= \env -> ccopyRef t env.ret (proj delayRef [delayIdx])

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
  ret t $ proj ref (fmap snd idxRefs)

retvalue (CSel _ chs sel) = do
  env <- R.ask

  (_, sref) <- rhsvalue ALocal sel
  recif env chs sref 0
  where
    -- TODO: binary tree if
    recif _ [] _ _ = error "recif: no choice (this is a bug)"
    recif _ [ch] _ _ = retvalue ch
    recif env (ch:chs) sref idx = allocLocal (TNumber TI32) $ \cond -> do
      cbinOp Eq sref (RConst (I32 idx)) cond
      cif cond (retvalue ch) (recif env chs sref (idx + 1))

toplevel :: Map Ident (CExpr FuncRef) -> Map FuncRef Func -> CallMBase (Map Ident ([Statement], [(Type, Idx)]))
toplevel toplevelMap funcRefMap = mdo
  refMap <- M.fromList <$> sequence
    [ case expr of
        CAbs _ fr -> pure (n, RFuncRef fr)
        _ -> do
          ref <- allocGlobal (cexprType expr)
          R.runReaderT (retvalue expr) (Env { bindings = refMap, ret = ref, to = [], localIdx = 0, allocations = [] })
          pure (n, ref)
    | (n, expr) <- M.toList toplevelMap
    ]

  funcMap <- M.fromList <$> sequence
    [ do
       stsa <- flip R.runReaderT (Env { bindings = refMap, ret = retRef, to = [], localIdx = 0, allocations = [] }) $ do
          sts <- cextract $ func f
          allocations <- R.asks (.allocations)
          pure (sts, allocations)
       pure (fr, stsa)
    | (fr, f@(Func _ params _ _)) <- M.toList funcRefMap
    -- Return ref is last param
    , let retRef = RArg (length params)
    ]

  pure $ M.fromList
    [ (n, stsa)
    | (fr, stsa) <- M.toList funcMap
    , Just n <- [ M.lookup fr funcRefToIdent ]
    ]

  where
    funcRefToIdent = M.fromList [ (fr, n) | (n, CAbs _ fr) <- M.toList toplevelMap ]

    func (Func _ params bindings body) = mdo
      bindingRefs <- mconcat <$> sequenceA
        [ pure $ M.fromList [ (p, RArg idx) | (idx, p) <- zip [0..] params ]
        , M.fromList <$> sequenceA
            [ (n,) . snd <$> R.local withBindingRefs (rhsvalue region bbody)
            | (n, region, bbody) <- bindings
            ]
        ]

      let withBindingRefs :: Env -> Env
          withBindingRefs Env {..} = Env { bindings = bindingRefs <> bindings, .. }

      R.local withBindingRefs $ retvalue body

-- TODO: local var indices should be function local?

-- TODO: oversampling just means that we insert some stateful code around the oversampled function (which we should always inline when generating code; this can happen directly in the codegen)
--- https://github.com/juce-framework/JUCE/blob/master/modules/juce_dsp/processors/juce_Oversampling.cpp
-- TODO: can't return Abs from Rec
-- NOTE: selection only happens after "opaque" transitions, e.g. function call or global ref; an array paired with a selection is a choice
-- TODO: generate SAbs code; pretty straightforward
-- TODO: replace refs to params with RArg 0, 1, 2 etc
-- TODO: rec and oversample take a lambda abstraction (or a Var pointing to a lambda abstraction)
-- TODO: zig std math: https://github.com/ziglang/zig/tree/master/lib/std/math
