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

module OSC.Codegen.Backend where

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
import qualified OSC.Expr.Comp as C
import OSC.Expr.Functors
import OSC.Expr.Defunc

import Debug.Trace

data Idx = IdxLocal Int | IdxGlobal Int deriving (Eq, Ord)

instance Show Idx where
  show (IdxLocal i) = "l" <> show i
  show (IdxGlobal i) = "g" <> show i

data Ref 
  = RArg Int
  | RRet

  | RConst Number

  | RVar Idx

  | RArr Type Idx
  | RProj {- source/dest -} Ref {- index -} Ref -- projection from or into array

  | RFuncRef FuncRef -- index into a global function table
  | RFuncRefRef Idx -- local or global var index with index into global function table (e.g. pointer to a function pointer)

showType :: Type -> String
showType (TNumber TI32) = "i32"
showType (TNumber TF32) = "f32"
showType (TNumber TI64) = "i64"
showType (TNumber TF64) = "f64"
showType (TArr t dim) = showType t <> "[" <> show dim <> "]"
showType (TLam [] retType) = "() -> " <> showType retType
showType (TLam params retType) = 
  "(" <> intercalate ", " (map showType params) <> ") -> " <> showType retType

instance Show Ref where
  show (RArg i) = "arg" <> show i
  show RRet = "ret"
  show (RConst n) = show n
  show (RVar idx) = show idx
  show (RArr t idx) = show idx <> ":" <> showType t
  show (RProj ref idx) = show ref <> "[" <> show idx <> "]"
  show (RFuncRef (FuncRef i)) = "f" <> show i
  show (RFuncRefRef idx) = show idx <> ":funcref"

data Instruction
  = SCopy Type {- source -} Ref {- dest -} Ref
  | SIf Ref [Instruction] [Instruction]
  | SCall {- funcref -} Ref {- args -} [Ref] {- return ref -} Ref
  | SBinOp Op {- a -} Ref {- b -} Ref {- result -} Ref
  | SFor {- counter -} Ref {- initial -} Int {- steps -} Int {- step -} Int [Instruction]

instance Show Instruction where
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

showBlock :: [Instruction] -> String
showBlock stmts = mconcat [ "  " <> line <> "\n" | stmt <- stmts, line <- lines (show stmt) ]

--------------------------------------------------------------------------------

{-

In WebAssembly, a "statically known" array is implemented by reserving a specific offset in Linear Memory. You then use i32.load and i32.store to read and write to that address. 
Here is a WAT (WebAssembly Text) example showing how to reserve an array of 10 integers starting at memory address 0, along with functions to get and set values.

(module
  ;; 1. Define memory. 1 page = 64KB.
  (memory (export "memory") 1)

  ;; 2. Optional: Pre-initialize the array with data at address 0
  ;; This puts [10, 20, 30] at the start of memory.
  (data (i32.const 0) "\0a\00\00\00\14\00\00\00\1e\00\00\00")

  ;; Function to SET a value: array[index] = value
  ;; The array starts at offset 0. Each i32 is 4 bytes.
  (func (export "set_array_val") (param $index i32) (param $value i32)
    ;; Calculate address: index * 4
    local.get $index
    i32.const 4
    i32.mul
    ;; Push value to store
    local.get $value
    ;; Store the value at (index * 4)
    i32.store
  )

  ;; Function to GET a value: return array[index]
  (func (export "get_array_val") (param $index i32) (result i32)
    ;; Calculate address: index * 4
    local.get $index
    i32.const 4
    i32.mul
    ;; Load from memory at that address
    i32.load
  )
)

Key Technical Details

    Addressing: Since memory is a byte array, you must multiply the index by the size of your type (4 bytes for i32, 8 for f64) to find the correct address. 
    Static Reservation: In a real project, you manually track which addresses are "reserved" for your static arrays. For example, if Array A is at 0-40, you might start Array B at address 44.
    Initialization: The (data ...) section allows you to bake initial values directly into the binary, which are loaded into memory when the module instantiates. 
    Security: Wasm checks bounds automatically. If you try to access an address beyond your allocated memory pages, it will trap (crash).

---

Using the offset parameter is the standard way to handle multiple static arrays without an allocator. You effectively partition your linear memory into fixed blocks.
Memory Layout Example
Imagine you want two static arrays:

    Array A: 10 integers (40 bytes), starting at address 0.
    Array B: 5 integers (20 bytes), starting at address 100. 

In WebAssembly, you don't "declare" these as separate objects; you simply use the immediate offset to target the correct starting point.

(module
  (memory (export "memory") 1)

  ;; --- ARRAY A (Starts at address 0) ---
  (func (export "set_A") (param $index i32) (param $val i32)
    local.get $index
    i32.const 4
    i32.mul
    local.get $val
    ;; No offset needed (or offset=0)
    i32.store 
  )

  ;; --- ARRAY B (Starts at address 100) ---
  (func (export "set_B") (param $index i32) (param $val i32)
    local.get $index
    i32.const 4
    i32.mul
    local.get $val
    ;; Static offset adds 100 to whatever index*4 is on the stack
    i32.store offset=100
  )

  ;; --- ARRAY B CONSTANT ACCESS ---
  ;; Accessing Array B's 3rd element (index 2) directly
  (func (export "get_B_const") (result i32)
    i32.const 0
    ;; Effective address = 0 + 100 (base) + 8 (index 2 * 4 bytes)
    i32.load offset=108 
  )
)

Why this is powerful

    Zero Runtime Cost: The engine adds the offset to the base address during the memory cycle. It's "free" math compared to doing an i32.add in code. 
    Virtual Structs: This is how C/Rust compilers handle structs. A "pointer" to a struct is pushed to the stack, and every field access uses i32.load offset=N where N is the field's position inside that struct. 
    Static Safety: By using a static offset for your "Base Address" and keeping your indices within bounds, you prevent your arrays from overlapping. 

Best Practices for Multiple Arrays

    Alignment: Try to align your starting offsets to 4 or 8 bytes. Wasm can handle unaligned loads, but they are often slower on some hardware. 
    Data Sections: Use the (data ...) section to pre-fill these specific regions.

(data (i32.const 0) "\01\02\03")   ;; Initial values for Array A
(data (i32.const 100) "\09\08\07") ;; Initial values for Array B

Shadow Stack: In complex modules, it is common to reserve the first few kilobytes for static data (like these arrays) and start your dynamic "heap" at a higher GLOBAL_BASE address (e.g., 1024). 

-}

-- WASM NOTES
-- we can return multiple values on the stack, but it's probably good to reserve this for small arrays only?
-- for larger arrays we can manage a linear mem shadow stack
-- globals scalars are WASM globals, global arrays go in linear mem
-- alignment is important

-- QUESTION: do we decide whether we return something on stack vs shadow stack etc here or do we leave it up to each backend?

data Config = Config
  { smallArrayMaxLength :: Int -- | Small arrays are returned on the stack
  }

data ProgramFunc = ProgramFunc
  { allocations :: Map Ident Type
  , instructions :: [Instruction]
  , needsShadowStack :: Bool
  } deriving Show

data Program = Program
  { globalAllocations :: Map Ident Type
  , funcMap :: Map FuncRef ProgramFunc
  , tickFunc :: ProgramFunc
  } deriving Show

type ExpA = Ann Type Expr

type CodegenM = ST.State ()

-- innerJoin :: Applicative f => Ord k => Map k (f a) -> Map k (f b) -> Map k (f (a, b))
-- innerJoin = M.intersectionWith (\fa fb -> (,) <$> fa <*> fb)

codegen :: Config -> DefuncMap (Ann Type) -> ExpA -> CodegenM Program
codegen cfg dfm = undefined
  where
    needsStackMap :: Map FuncRef Bool
    needsStackMap = fmap funcNeedsStack dfm.funcMap
      where
        funcNeedsStack (C.LamAnn typ _ bindings body) = or
          [ C.sizeOfType typ > cfg.smallArrayMaxLength
          , or [ M.findWithDefault False fr needsStackMap | Func fr <- universe body ]
          , or [ M.findWithDefault False fr needsStackMap | (_, _, bbody) <- bindings, Func fr <- universe bbody ]
          ]

    collectLamAllocations :: C.LamAnn ExpA -> ([Type], [Type])
    collectLamAllocations (C.LamAnn typ _ bindings _) = mconcat
      [ case region of
          C.AllocLocal -> ([t], [])
          C.AllocGlobal -> ([], [t])
      | (_, region, Ann (t, _)) <- bindings
      ]


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