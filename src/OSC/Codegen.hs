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

data Ref
  = RConst Number
  | RRet Type
  | RArg Type Ident
  | RVar Type Location
  | RProj {- expression -} Ref {- index -} Ref {- inner dimension, e.g. for the array[4][7], array[1] would set the inner dimension to 7 -} Int
  | RFuncRef FuncRef
  deriving Show

data SliceRoot = SArg Ident | SVar Location | SRet
  deriving Show

data Slice
  = SConst Number
  | SSlice Type {- arg or var or ret -} SliceRoot {- offset -} (Either Int Location) {- length -} Int
  | SFuncRef FuncRef
  deriving Show

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

data Instruction
  = ICopy {- dest -} Slice {- source -} Slice
  | IIf Slice [Instruction] [Instruction]
  | ICall {- return ref -} Slice {- funcref -} Slice [Slice]
  | IBinOp Op {- result -} Slice {- a -} Slice {- b -} Slice
  | IFor {- counter -} Location {- initial -} Int {- steps -} Int {- step -} Int [Instruction]
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
-------- [] elim static indices [a, b, c][1] == b, { x: a, y: 6 }.x == a
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
  , locals :: [(Ident, Type)]
  , instructions :: [Instruction]
  } deriving Show

data Value = VNumber Number | VArr [Value]
  deriving Show

data Program = Program
  { globals :: Map Ident Type
  , funcMap :: Map FuncRef ProgramFunc
  , tick :: [Instruction]
  , startup :: [Instruction]
  } deriving Show

data RecEnv = RecEnv
  { delayBuffer :: Ref
  , writeIdx :: Ref
  , readIdx :: Ref
  }

data Env = Env
  { varMap :: Map Ident Ref
  , recMap :: Map Ident RecEnv
  }

type AllocM = ST.State (Int, Map Location Type)

type CodegenM = R.ReaderT Env (W.WriterT [Instruction] AllocM)

allocLoc :: (Int -> Location) -> Type -> AllocM Location
allocLoc region typ = ST.state $ \(idx, m) -> (region idx, (idx + 1, M.insert (region idx) typ m))

alloc :: Type -> CodegenM Ref
alloc typ = fmap (RVar typ) $ lift $ lift $ allocLoc Local typ

-- array[5][6][3]
-- array[2] :: array[6][3] so slice length is 6 * 3 and offset is 2 * 6 * 3
-- array[2][4] :: array[3] so slice length is 3 and offset is 2 * 6 * 3 + 4 * 3 or (2 * 6 + 4) * 3

-- array[6][3]
-- array[2] :: array[3] so slice length is 3 and offset is 2 * 3

-- array[3]
-- array[2] :: i32 (for example) so slice length is 1 and offset is 2 * 1

toSlice :: Ref -> CodegenM Slice
toSlice (RConst n) = pure $ SConst n
toSlice (RFuncRef fr) = pure $ SFuncRef fr
toSlice (RArg typ arg) = pure $ SSlice typ (SArg arg) (Left 0) (C.elemCountOfType typ)
toSlice (RVar typ loc) = pure $ SSlice typ (SVar loc) (Left 0) (C.elemCountOfType typ)
toSlice (RRet typ) = pure $ SSlice typ SRet (Left 0) (C.elemCountOfType typ)
toSlice (RProj ref idx innerDim) = do
  slice <- toSlice ref
  idxSlice <- toSlice idx
  
  case (slice, idxSlice) of
    -- Constant index with constant offset - compute statically
    (SSlice typ loc (Left offset) _, SConst (I32 i)) ->
      pure $ SSlice typ loc (Left (offset + i * innerDim)) innerDim
    (SSlice typ loc (Left offset) _, SConst (I64 i)) ->
      pure $ SSlice typ loc (Left (offset + i * innerDim)) innerDim
    
    -- Dynamic cases - need to compute offset at runtime
    (SSlice typ loc baseOffset _, _) -> do
      offsetLoc <- lift $ lift $ allocLoc Local C.ti32
      let offsetVar = RVar C.ti32 offsetLoc

      -- Load index into offset variable
      case idxSlice of
        SConst n
          | C.numberType n == TNumber TI32 -> copyRef offsetVar (RConst n)
        SSlice (TNumber TI32) (SArg arg) (Left 0) 1 -> copyRef offsetVar (RArg C.ti32 arg)
        SSlice (TNumber TI32) (SVar loc) (Left 0) 1 -> copyRef offsetVar (RVar C.ti32 loc)
        _ -> error $ "toSlice: unexpected index slice type: " <> show idxSlice
      
      -- Multiply by inner dimension
      binOp Mul offsetVar (RConst $ I32 innerDim) offsetVar
      
      -- Add base offset
      case baseOffset of
        Left offset -> when (offset /= 0) $ do
          binOp Add offsetVar (RConst $ I32 offset) offsetVar
        Right baseLoc -> do
          binOp Add offsetVar (RVar C.ti32 baseLoc) offsetVar
      
      pure $ SSlice typ loc (Right offsetLoc) innerDim
    
    _ -> error "toSlice: projection of non-variable slice"

copyRef :: Ref -> Ref -> CodegenM ()
copyRef dst src = do
  dstSlice <- toSlice dst
  srcSlice <- toSlice src
  
  lift $ W.tell [ICopy dstSlice srcSlice]

binOp :: Op -> Ref -> Ref -> Ref -> CodegenM ()
binOp op dest a b = do
  destSlice <- toSlice dest
  aSlice <- toSlice a
  bSlice <- toSlice b
  lift $ W.tell [IBinOp op destSlice aSlice bSlice]

call :: Ref -> Ref -> [Ref] -> CodegenM ()
call dest funcRef args = do
  destSlice <- toSlice dest
  funcRefSlice <- toSlice funcRef
  argSlices <- traverse toSlice args
  lift $ W.tell [ICall destSlice funcRefSlice argSlices]

if_ :: Ref -> CodegenM () -> CodegenM () -> CodegenM ()
if_ cond t e = do
  env <- R.ask
  ((), t') <- lift $ lift $ runWriterT $ runReaderT t env
  ((), e') <- lift $ lift $ runWriterT $ runReaderT e env
  condSlice <- toSlice cond
  lift $ W.tell [IIf condSlice t' e']

innerDims :: Type -> [Int]
innerDims (TArr (TArr t dim) _) = dim:innerDims t
innerDims (TArr _ _) = [1]
innerDims _ = error "innerDims"

codegen :: DefuncMap (Ann Type) -> Ann Type Expr -> CodegenM Program
codegen dfm expr = do
  lamAllocs <- mconcat <$> traverse (lift . lift . collectLamAllocations) (M.elems dfm.funcMap)
  (recAllocs, recEnvs) <- mconcat <$> traverse (lift . lift . collectRecAllocations) dfm.recs
  undefined
  where
    collectLamAllocations :: C.LamAnn (Ann Type Expr) -> AllocM (Map Ident Ref)
    collectLamAllocations (C.LamAnn _ _ bindings _) = M.fromList <$> sequence
      [ do
          loc <- allocLoc Global typ
          pure (n, RVar typ loc)
      | (n, C.AllocGlobal, Ann (typ, _)) <- bindings
      ]

    collectRecAllocations :: C.RecAnn (Ann Type Expr) -> AllocM (Map Ident Ref, Map Ident RecEnv)
    collectRecAllocations (C.RecAnn typ delay param bindings _) = do
      varMap <- sequence
        [ do
            loc <- allocLoc Global typ
            pure (n, RVar typ loc)
        | (n, C.AllocGlobal, Ann (typ, _)) <- bindings
        ]
      
      delayBuffer <- RVar (TArr typ delay) <$> allocLoc Global (TArr typ delay)
      writeIdx <- RVar C.ti32 <$> allocLoc Global C.ti32
      readIdx <- RVar C.ti32 <$> allocLoc Global C.ti32

      pure (M.fromList varMap, M.singleton param (RecEnv {..}))

    genLam :: Env -> C.LamAnn (Ann Type Expr) -> CodegenM ()
    genLam env (C.LamAnn typ params bindings body) = mdo
       bindingRefs <- mconcat <$> sequenceA
         -- Arguments
         [ pure $ M.fromList [ (p, RArg typ p) | (p, typ) <- zip params (C.paramTypes "genLam" typ) ]

         -- Bindings (must be in topsort order)
         , M.fromList <$> sequenceA
             [ case region of
                 C.AllocLocal -> (n,) <$> R.local withBindingRefs (rhs bbody)
                 C.AllocGlobal -> do
                   -- Set global ref as return value for binding rhs
                   ret <- R.asks ((M.! n) . (.varMap))
                   gen ret bbody
                   pure (n, ret)
             | (n, region, bbody) <- bindings
             ]
         ]

       let withBindingRefs :: Env -> Env
           withBindingRefs Env {..} = Env { varMap = bindingRefs <> varMap, .. }

       R.local withBindingRefs $ gen (RRet typ) body

    genRec :: C.RecAnn (Ann Type Expr) -> CodegenM ()
    genRec (C.RecAnn typ delay param bindings body) = do
      env <- R.ask
      let recEnv = env.recMap M.! param

      mdo
        bindingRefs <- mconcat <$> sequenceA
          [ pure $ M.singleton param (RProj recEnv.delayBuffer recEnv.readIdx 1)
          , M.fromList <$> sequenceA [ (n,) <$> R.local withBindingRefs (rhs bbody) | (n, _, bbody) <- bindings ]
          ]

        let withBindingRefs :: Env -> Env
            withBindingRefs Env {..} = Env { varMap = bindingRefs <> varMap, .. }

        R.local withBindingRefs $ gen (RProj recEnv.delayBuffer recEnv.writeIdx 1) body

        -- Increment read & write index
        binOp Add recEnv.writeIdx (RConst $ I32 1) recEnv.writeIdx
        binOp Mod recEnv.writeIdx (RConst $ I32 delay) recEnv.writeIdx
      
        -- TODO: variable delay
        binOp Add recEnv.readIdx (RConst $ I32 1) recEnv.readIdx
        binOp Mod recEnv.readIdx (RConst $ I32 delay) recEnv.readIdx
    
    pfoldedSelectR body@(Ann (bodyTyp, _)) idxs = do
      bodyVar <- alloc bodyTyp
      gen bodyVar body
      idxVars <- traverse rhs idxs
      pure $ foldr (\(idx, dim) body' -> RProj body' idx dim) bodyVar (zip idxVars (scanl1 (*) (innerDims bodyTyp)))

    prec param = do
      env <- R.ask
      let envRec = env.recMap M.! param
      pure (RProj envRec.delayBuffer envRec.readIdx 1)

    rhs :: Ann Type Expr -> CodegenM Ref
    rhs (Ann (_, PConst n)) = pure $ RConst n
    rhs (Ann (_, PFunc fr)) = pure $ RFuncRef fr

    rhs (Ann (_, PVar n)) = R.ask >>= \env -> pure (env.varMap M.! n)

    rhs e@(Ann (typ, PArr _)) = alloc typ >>= \var -> gen var e >> pure var
    rhs e@(Ann (typ, POp _ _ _)) = alloc typ >>= \var -> gen var e >> pure var
    rhs e@(Ann (typ, PApp _ _)) = alloc typ >>= \var -> gen var e >> pure var
    rhs e@(Ann (typ, PFoldedSelectL _ _)) = alloc typ >>= \var -> gen var e >> pure var

    rhs (Ann (_, PFoldedSelectR body idxs)) = pfoldedSelectR body idxs
    rhs (Ann (_, (PRec param))) = prec param

    ---
    
    gen :: Ref -> Ann Type Expr -> CodegenM ()
    gen ret (Ann (_, PConst n)) = copyRef ret (RConst n)
    gen ret (Ann (_, PFunc fr)) = copyRef ret (RFuncRef fr)

    gen ret (Ann (_, PVar n)) = R.ask >>= \env -> copyRef ret (env.varMap M.! n)

    gen ret (Ann (typ, PArr elems)) = do
      let innerDim = product $ innerDims typ
      sequence_
        [ gen (RProj ret (RConst (C.I32 i)) innerDim) elem
        | (i, elem) <- zip [0..] elems
        ]

    gen ret (Ann (_, POp op a b)) = do
      avar <- rhs a
      bvar <- rhs b
      binOp op ret avar bvar

    gen ret (Ann (_, (PApp f args))) = do
      rargs <- traverse rhs args

      case f of
        Ann (_, PFunc fr) -> call ret (RFuncRef fr) rargs
        _ -> do
          fvar <- rhs f
          call ret fvar rargs

    gen ret (Ann (_, (PFoldedSelectL elems idx@(Ann (idxTyp, _))))) = do
      condVar <- alloc C.ti32
      idxVar <- rhs idx

      let mkRef = case idxTyp of
            TNumber TI32 -> RConst . I32
            TNumber TI64 -> RConst . I64
            _ -> error "eqRef"

      -- TODO: binary tree if
      let recIf [] _ = error "recif: no choice (this is a bug)"
          recIf [elem] _ = gen ret elem
          recIf (elem:elems) i = do
            binOp Eq condVar (mkRef i) idxVar
            if_ condVar (gen ret elem) (recIf elems (i + 1))

      recIf elems 0

    gen ret (Ann (_, PFoldedSelectR body idxs)) = copyRef ret =<< pfoldedSelectR body idxs
    gen ret (Ann (_, (PRec param))) = copyRef ret =<< prec param
    
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
