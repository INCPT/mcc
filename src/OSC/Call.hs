{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module OSC.Call where

import Data.Functor.Identity (Identity (Identity))
import Control.Monad (when)
import Control.Monad.Fix (MonadFix)
import Control.Monad.Trans (MonadTrans, lift)
import qualified Control.Monad.Reader as R
import Control.Monad.Reader (ReaderT, local, asks, ask, runReaderT)
import qualified Control.Monad.State.Lazy as ST
import Control.Monad.State.Lazy (StateT, State, state, runState, runStateT)
import qualified Control.Monad.Trans.Writer as W
import Data.Functor.Product (Product (Pair))
import Data.Map (Map)
import Data.List (intercalate)
import qualified Data.Map as M
import Control.Monad.Free (Free (Free, Pure), liftF)
import qualified Control.Monad.Trans.Free as TF
import Control.Monad.Trans.Free (FreeT (FreeT), FreeF)
import OSC.Ctx

data Idx = Local Int | Global Int deriving (Eq, Ord)

instance Show Idx where
  show (Local i) = "l" <> show i
  show (Global i) = "g" <> show i

data Ref 
  = RArg Int
  | RRet

  | RConst Number

  | RVar Idx -- either a function local var index (e.g. in function f() { int a; float b; } would be locals with index 0 and 1) or an index into a global var table

  | RArr Type Idx -- global base address of array in a linear memory layout
  | RProj {- source/dest -} Ref {- index -} Ref -- projection from or into array

  | RFuncRef FuncRef -- index into a global function table
  | RFuncRefRef Idx -- local or global var index with index into global function table (e.g. pointer to a function pointer)

instance Show Ref where
  show (RArg i) = "arg" <> show i
  show RRet = "ret"
  show (RConst n) = show n
  show (RVar idx) = show idx
  show (RArr t idx) = show idx <> ":" <> showType t
  show (RProj ref idx) = show ref <> "[" <> show idx <> "]"
  show (RFuncRef (FuncRef i)) = "f" <> show i
  show (RFuncRefRef idx) = show idx <> ":funcref"

data Statement
  = SCopy Type {- source -} Ref {- dest -} Ref
  | SIf Ref [Statement] [Statement]
  | SCall {- funcref -} Ref {- args -} [Ref] {- return ref -} Ref
  | SBinOp Op {- a -} Ref {- b -} Ref {- result -} Ref
  | SFor {- counter -} Ref {- initial -} Int {- steps -} Int {- step -} Int [Statement]

instance Show Statement where
  show (SCopy t src dst) = show dst <> " := " <> show src
  show (SIf cond thn els) = mconcat
    [ "if " <> show cond <> " {\n"
    , showBlock thn
    , "} else {\n"
    , showBlock els
    , "}"
    ]
  show (SCall funcRef args ret) = show ret <> " := " <> show funcRef <> "(" <> intercalate ", " (fmap show args) <> ")"
  show (SBinOp op a b res) = show res <> " := " <> show a <> " " <> show op <> " " <> show b
  show (SFor counter initial steps step body) = mconcat
    [ "for " <> show counter <> " = " <> show initial <> " to " <> show steps <> " step " <> show step <> " {\n"
    , showBlock body
    , "}"
    ]

showBlock :: [Statement] -> String
showBlock stmts = mconcat [ "  " <> line <> "\n" | stmt <- stmts, line <- lines (show stmt) ]

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

data LocalState = LocalState
  { nextVarIdx :: Int
  , allocations :: [(Type, Idx)]
  }

data GlobalState = GlobalState
  { nextVarIdx :: Int
  , nextFuncRefIdx :: Int
  , allocations :: [(Type, Idx)]
  }

type CallMBase = W.WriterT [Statement] (StateT LocalState (State GlobalState))
type CallM = ReaderT Env CallMBase

allocBase :: Monad m => ((Idx -> Ref) -> StateT st m Ref) -> Type -> StateT st m Ref
allocBase alloc t = case t of
  TNumber _ -> alloc RVar
  TArr _ _ -> alloc (RArr t)
  TAbs _ _ -> alloc RFuncRefRef

allocLocal :: forall m. Monad m => Type -> StateT LocalState m Ref
allocLocal t = flip allocBase t $ \mkRef -> fmap mkRef $ state $ \LocalState {..} ->
  (Local nextVarIdx, LocalState { nextVarIdx = nextVarIdx + 1, allocations = (t, Local nextVarIdx):allocations, .. })

allocGlobal :: Type -> State GlobalState Ref
allocGlobal t = flip allocBase t $ \mkRef -> fmap mkRef $ state $ \GlobalState {..} ->
  (Global nextVarIdx, GlobalState { nextVarIdx = nextVarIdx + 1, allocations = (t, Global nextVarIdx):allocations, .. })

--------------------------------------------------------------------------------

cextract :: CallM () -> CallM [Statement]
cextract m = do
  env <- ask
  fmap snd $ lift $ lift $ W.runWriterT (runReaderT m env)

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
  i <- lift $ lift $ allocLocal (TNumber TI32)
  f' <- cextract (f i)
  lift $ W.tell [SFor i initial steps step f']

--------------------------------------------------------------------------------

allocAndStore :: AllocRegion -> CExpr FuncRef -> CallM (Type, Ref)
allocAndStore ALocal e = do
  ref <- lift $ lift $ allocLocal t
  local (\Env {..} -> Env { ret = ref, to = [], .. }) (retvalue e)
  pure (t, ref)
  where
    t = cexprType e
allocAndStore AGlobal e = do
  ref <- lift $ lift $ lift $ allocGlobal t
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
    _ -> error $ "rhsvalue: unknown global (this is a bug): " <> show n
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
  | otherwise = mdo
      -- Alloc delay number of samples of type t[]
      delayRef <- lift $ lift $ lift $ allocGlobal (TArr t delay)
      delayIdx <- lift $ lift $ lift $ allocGlobal (TNumber TI32)

      bindingRefs <- mconcat <$> sequenceA
        [ pure $ M.singleton param (proj delayRef [delayIdx])
        , M.fromList <$> sequenceA [ (n,) . snd <$> local withBindingRefs (rhsvalue region bbody) | (n, region, bbody) <- bindings ]
        ]

      let withBindingRefs :: Env -> Env
          withBindingRefs Env {..} = Env { bindings = bindingRefs <> bindings, .. }

      local withBindingRefs $ retvalue body
      
      -- Copy result to delay line
      ask >>= \env -> ccopyRef t env.ret (proj delayRef [delayIdx])

      cbinOp Add delayIdx (RConst $ I32 1) delayIdx
      cbinOp Mod delayIdx (RConst $ I32 delay) delayIdx
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
  env <- ask

  (_, sref) <- rhsvalue ALocal sel
  recif env chs sref 0
  where
    -- TODO: binary tree if
    recif _ [] _ _ = error "recif: no choice (this is a bug)"
    recif _ [ch] _ _ = retvalue ch
    recif env (ch:chs) sref idx = do
      cond <- lift $ lift $ allocLocal (TNumber TI32)
      cbinOp Eq sref (RConst (I32 idx)) cond
      cif cond (retvalue ch) (recif env chs sref (idx + 1))

--------------------------------------------------------------------------------

data IRFunc = IRFunc
  { allocations :: [(Type, Idx)]
  , statements :: [Statement]
  } deriving Show

data IR = IR
  { toplevelAllocations :: [(Type, Idx)]
  , toplevelStatements :: [Statement]
  , toplevelFuncs :: Map Ident FuncRef
  , funcMap :: Map FuncRef IRFunc
  } deriving Show

data IR2 = IR2
  { allocations :: [(Type, Idx)]
  , toplevelStatements :: [Statement]
  , funcMap :: Map FuncRef IRFunc
  , main :: Ref
  } deriving Show

toplevel2 :: Map Ident Type -> Map FuncRef Func -> CExpr FuncRef -> IR2
toplevel2 globals funcRefMap expr = IR2 { allocations = st.allocations, .. }
  where
    (bla, st) = runState gen (GlobalState { nextVarIdx = 0, nextFuncRefIdx = 0, allocations = [] })
    -- toplevelFuncs = M.fromList [ (n, fr) | (n, CAbs _ fr) <- M.toList toplevelMap ]

    gen :: State GlobalState Ref
    gen = do
      globalRefs <- M.fromList <$> sequence [ (n,) <$> allocGlobal t | (n, t) <- M.toList globals ]

      main <- case expr of
        CAbs _ fr -> pure $ RFuncRef fr
        _ -> error "toplevel: definition is not a function"

      funcMap <- M.fromList <$> sequence
        [ do
           (((), sts), lst) <-
              (flip runStateT undefined . W.runWriterT . flip runReaderT (Env { bindings = globalRefs, ret = RRet, to = [], localIdx = 0, allocations = [] })) $ func f
           pure (fr, undefined)
        | (fr, f) <- M.toList funcRefMap
        ]
      
      pure undefined

      where
        func (Func _ params bindings body) = mdo
          bindingRefs <- mconcat <$> sequenceA
            -- Arguments
            [ pure $ M.fromList [ (p, RArg idx) | (idx, p) <- zip [0..] params ]

            -- Bindings
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

{-
toplevel :: Map Ident Type -> Map Ident (CExpr FuncRef) -> Map FuncRef Func -> IR
toplevel globals toplevelMap funcRefMap = IR { toplevelAllocations = st.allocations, .. }
  where
    ((funcMap, toplevelStatements), st) = runState (W.runWriterT gen) (GlobalState { nextVarIdx = 0, nextFuncRefIdx = 0, allocations = [] })
    toplevelFuncs = M.fromList [ (n, fr) | (n, CAbs _ fr) <- M.toList toplevelMap ]

    gen = mdo
      refMap <- fmap M.fromList $ sequence $ mconcat
        -- Gloabls
        [ [ (n,) <$> allocGlobal t | (n, t) <- M.toList globals ]

        -- Toplevel bindings
        , [ case expr of
              CAbs _ fr -> pure (n, RFuncRef fr)
              _ -> do
                ref <- allocGlobal (cexprType expr)
                runReaderT (retvalue expr) (Env { bindings = refMap, ret = ref, to = [], localIdx = 0, allocations = [] })
                pure (n, ref)
          | (n, expr) <- M.toList toplevelMap
          ]
        ]

      M.fromList <$> sequence
        [ do
           irf <- flip runReaderT (Env { bindings = refMap, ret = RRet, to = [], localIdx = 0, allocations = [] }) $ do
              statements <- cextract $ func f
              allocations <- asks (.allocations)
              pure IRFunc {..}
           pure (fr, irf)
        | (fr, f) <- M.toList funcRefMap
        ]
      where
        func (Func _ params bindings body) = mdo
          bindingRefs <- mconcat <$> sequenceA
            -- Arguments
            [ pure $ M.fromList [ (p, RArg idx) | (idx, p) <- zip [0..] params ]

            -- Bindings
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

-- RJCT: topsort global statements

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

--------------------------------------------------------------------------------

