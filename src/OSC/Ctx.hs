{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}

module OSC.Ctx where

import Data.Bifunctor (first, second)
import Data.Data (Typeable, Data)
import Data.Functor.Identity
import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set, (\\))
import qualified Data.Set as S
import Control.Monad.Trans (MonadTrans, lift)
import qualified Control.Monad.Reader as R
import qualified Control.Monad.State as ST
import qualified Control.Monad.Trans.Writer.CPS as W
import Data.Generics.Uniplate.Data
import Data.Generics.Str

data TNumber = TI32 | TF32 | TI64 | TF64 deriving Data

data Type = TNumber TNumber | TArr Type {- length -} Int | TAbs [Type] Type
  deriving Data

sizeOfType :: Type -> Int
sizeOfType (TNumber TI32) = 4
sizeOfType (TNumber TF32) = 4
sizeOfType (TNumber TI64) = 8
sizeOfType (TNumber TF64) = 8
sizeOfType (TArr t dim) = sizeOfType t * dim
sizeOfType (TAbs _ _) = sizeOfType (TNumber TI32) -- TODO PLATFORM: funcref is I32

returnType :: Type -> Type
returnType t@(TArr _ _) = t
returnType (TAbs _ t) = t
returnType t = t

peelType :: Type -> Type
peelType (TArr t _) = t
peelType (TAbs _ _) = error "peelType: abstraction"
peelType t = error $ "peelType: " <> show t

paramTypes :: Type -> [Type]
paramTypes (TArr _ _) = []
paramTypes (TAbs params _) = params
paramTypes _ = []

data Number = I32 Int | I64 Int | F32 Float | F64 Double
  deriving (Show, Data)

numberType :: Number -> Type
numberType (I32 _) = TNumber TI32
numberType (F32 _) = TNumber TF32
numberType (I64 _) = TNumber TI64
numberType (F64 _) = TNumber TF64

data Ident = Ident String
  deriving (Eq, Ord, Data, Show)

data Op = Add | Sub | Mul | Div | Mod | And | Or | Xor | Shl | Shr | Rotl | Rotr 
        | Eq | Ne | Gt | Lt | GEt | LEt 
        | Min | Max | CopySign | Rem
  deriving (Data, Show)

data UOp = Sqrt | Abs' | Neg | Ceil | Floor | Trunc | Nearest 
         | Clz | Ctz | Popcnt | Eqz
         | Extend | Wrap | Convert | Demote | Promote | Reinterpret
  deriving (Data, Show)

data Expr
  = EConst Number
  | EOp Type Op Expr Expr -- both args and the result are simple types
  | EArr Type [Expr]

  | EVar Type Ident

  | EAbs Type {- params -} [Ident] {- bindings -} [(Ident, Expr)] {- body -} Expr
  | EApp Type Expr [Expr]

  | ESelect Type Expr {- selector -} Expr

  -- NOTE: The (return) type of a recursive expression can not contain abstractions
  -- in order to simplify the logic and not require an initial value. It wouldn't make
  -- much sense generally anyway.
  | ERec Type {- delay -} Int {- must be of type abstraction -} Ident {- bindings -} [(Ident, Expr)] {- body -} Expr
  deriving Show

exprType :: Expr -> Type
exprType (EConst n) = numberType n
exprType (EOp t _ _ _) = t
exprType (EArr t _) = t
exprType (EVar t _) = t
exprType (EAbs t _ _ _) = t
exprType (EApp t _ _) = t
exprType (ESelect t _ _) = t
exprType (ERec t _ _ _ _) = t

--------------------------------------------------------------------------------

type StackM s m a = ST.StateT [s] m a

push :: Monad m => s -> StackM s m ()
push s = ST.modify (s:)

pop :: Monad m => StackM s m (Maybe s)
pop = do
  as <- ST.get
  case as of
    (a:as) -> do
      ST.put as
      pure (Just a)
    _ -> pure Nothing

runStack :: StackM s Identity a -> a
runStack = flip ST.evalState []

--------------------------------------------------------------------------------

-- * TODO: in typechecking, check that static indices are within range
-- ** even better: attach range to index; then check if everything ok in range check
-- ***  otherwise expect a clamp() or wrap() range correcting fun
-- ** if not possible, then demand clamp/wrap in dynamic select index expressions
-- * TODO: in the CallM monad, arguments that get written to the output can pass their array ctx slice to the argument expression, so no need for copy

-- TODO: optimization is performed on the CExpr datatype

-- TODO: alignment in AllocM!

-- TODO: what happens if part of the return value is a capture?
-- this is basically return value ref propagation up the binding chain
-- the most recent returned binding (or argument) gets tagged with "write to return value ref"

newtype FuncRef = FuncRef Int deriving (Eq, Ord, Data, Show)

data AllocRegion = ALocal | AGlobal
  deriving (Show, Data)

data CIndexable abs
  = CVar Type Ident
  | CApp Type (CExpr abs) [CExpr abs]
  | CRec Type {- delay -} Int {- must be of type abstraction -} {- params -} Ident {- bindings -} [(Ident, AllocRegion, CExpr abs)] (CExpr abs)
  deriving Data

data CExpr abs
  = CSel Type [CExpr abs] {- selector -} (CExpr abs)
  | CIndexed [(Type, CExpr abs)] (CIndexable abs) -- selection indices that flow into the inner expression
  | CArr Type [CExpr abs]
  | CConst Number
  | COp Type Op (CExpr abs) (CExpr abs)
  | CAbs Type abs
  deriving Data

cexprType :: CExpr abs -> Type
cexprType (CSel t _ _) = t
cexprType (CIndexed idxs expr) = peelOffIndices (length idxs) (indexableType expr)
  where
    peelOffIndices :: Int -> Type -> Type
    peelOffIndices 0 t = t
    peelOffIndices n (TArr t _) = peelOffIndices (n - 1) t
    peelOffIndices _ t = error $ "cexprType: cannot peel " <> show (length idxs) <> " indices from type " <> show t <> " (this is a bug)"
cexprType (CArr t _) = t
cexprType (CConst n) = numberType n
cexprType (COp t _ _ _) = t
cexprType (CAbs t _) = t

indexableType :: CIndexable abs -> Type
indexableType (CVar t _) = t
indexableType (CApp t _ _) = t
indexableType (CRec t _ _ _ _) = t

--------------------------------------------------------------------------------

showAbs :: Show abs => [Ident] -> [(Ident, AllocRegion, CExpr abs)] -> CExpr abs -> String
showAbs params bs body =
  "λ" <> showParams params <> " " <> showBindings bs <> " = " <> show body
  where
    showParams [] = "()"
    showParams ps = "(" <> intercalate ", " (map (\(Ident n) -> n) ps) <> ")"
  
    showBindings [] = ""
    showBindings bindings = "{ " <> intercalate "; " (map showBinding bindings) <> " }"
    showBinding (Ident n, region, expr) = 
      n <> "@" <> showRegion region <> " = " <> show expr
    showRegion ALocal = "local"
    showRegion AGlobal = "global"

instance Show Abs where
  show (Abs params bs body) = showAbs params bs body

instance Show abs => Show (CIndexable abs) where
  show (CVar _ (Ident n)) = n
  show (CApp _ f a) = show f <> "(" <> intercalate ", " (map show a) <> ")"
  show (CRec t delay param bs body) = "rec[" <> showType t <> ", delay=" <> show delay <> "](" <> showAbs [param] bs body <> ")"

instance Show abs => Show (CExpr abs) where
  show (CSel t cs idx) = 
    "choice[" <> showType t <> "](" <> intercalate " | " (map show cs) <> ")[" <> show idx <> "]"
  show (CIndexed [] expr) = show expr
  show (CIndexed idxs expr) = 
    show expr <> " @ [" <> intercalate ", " (map showIdxPair idxs) <> "]"
    where
      showIdxPair (t, idx) = showType t <> "[" <> show idx <> "]"
  show (CArr t cs) = "[" <> showType t <> ": " <> intercalate ", " (map show cs) <> "]"
  show (CConst n) = show n
  show (COp _ op a b) = "(" <> show a <> " " <> showOp op <> " " <> show b <> ")"
  show (CAbs _ abs) = show abs

instance Show Type where
  show = showType

showType :: Type -> String
showType (TNumber TI32) = "i32"
showType (TNumber TF32) = "f32"
showType (TNumber TI64) = "i64"
showType (TNumber TF64) = "f64"
showType (TArr t dim) = showType t <> "[" <> show dim <> "]"
showType (TAbs [] retType) = "() -> " <> showType retType
showType (TAbs params retType) = 
  "(" <> intercalate ", " (map showType params) <> ") -> " <> showType retType

showOp :: Op -> String
showOp Add = "+"
showOp Sub = "-"
showOp Mul = "*"
showOp Div = "/"
showOp Mod = "%"
showOp And = "&"
showOp Or = "|"
showOp Xor = "^"
showOp Shl = "<<"
showOp Shr = ">>"
showOp Rotl = "rotl"
showOp Rotr = "rotr"
showOp Eq = "=="
showOp Ne = "!="
showOp Gt = ">"
showOp Lt = "<"
showOp GEt = ">="
showOp LEt = "<="
showOp Min = "min"
showOp Max = "max"
showOp CopySign = "copysign"
showOp Rem = "rem"

--------------------------------------------------------------------------------

toC :: Monad m => CIndexable Abs -> StackM (Type, Expr) m (CExpr Abs)
toC e = do
  idxs <- ST.get
  pure $ CIndexed (map (second toCExpr) idxs) e

-- Pair each index with the appropriate array, so an an expression like
-- `[[0, 1], [2, 3]][1][0]` turns into `[[0, 1][0], [2, 3][0]][1]`.
-- This allows for easy constant index elimination and the generation of more efficient code.
choiceTree :: Monad m => Expr -> StackM (Type, Expr) m (CExpr Abs)
choiceTree (EConst n) = do
  idxs <- ST.get
  pure $ case idxs of
    [] -> CConst n
    _ -> error "choiceTree: cannot index into a constant (this is a bug)"
choiceTree (EOp t op a b) = do
  idxs <- ST.get
  case idxs of
    [] -> pure $ COp t op (toCExpr a) (toCExpr b)
    _ -> error "choiceTree: cannot index into an operation result (this is a bug)"
choiceTree (EVar t n) = toC (CVar t n)
choiceTree (EApp t f as) = toC (CApp t (toCExpr f) (fmap toCExpr as))
choiceTree (EAbs t params bs body) = do
  idxs <- ST.get
  pure $ case idxs of
    [] -> CAbs t (Abs params [ (n, ALocal, toCExpr b) | (n, b) <- bs ] (toCExpr body))
    _ -> error "choiceTree: cannot index into an abstraction (this is a bug)"
choiceTree (ERec t d param bs body) = toC (CRec t d param [ (n, ALocal, toCExpr b) | (n, b) <- bs ] (toCExpr body))
choiceTree (EArr t es) = do
  s <- pop
  case s of
    Just (t, idx) -> do
      es' <- traverse choiceTree es
      push (t, idx)
      pure $ CSel t es' (toCExpr idx)
    Nothing -> pure $ CArr t (map toCExpr es)
choiceTree (ESelect t e idx) = do
  push (t, idx)
  c <- choiceTree e
  _ <- pop
  pure c

--------------------------------------------------------------------------------

elimConstIndices :: CExpr Abs -> CExpr Abs
elimConstIndices = transform go
  where
    go :: CExpr Abs -> CExpr Abs

    -- Eliminate constant index selections by directly selecting the choice
    -- It's ok to prune impure expressions here (since the index is constant those expressions will never be accessible)
    go (CSel _ chs (CConst (I32 idx))) = chs !! idx
    go (CSel _ chs (CConst (I64 idx))) = chs !! idx

    -- Keep everything else as-is
    go ch = ch

optimize :: CExpr Abs -> CExpr Abs
optimize = elimConstIndices

toCExpr :: Expr -> CExpr Abs
toCExpr = optimize . flip ST.evalState [] . choiceTree

--------------------------------------------------------------------------------

newtype Unique a = Unique (ST.State Int a)
  deriving (Functor, Applicative, Monad)

runUnique :: Unique a -> a
runUnique (Unique m) = ST.evalState m 0

fresh :: Unique Ident
fresh = Unique $ do
  n <- ST.get
  ST.put (n + 1)
  pure $ Ident ("_captured_" <> show n)

--------------------------------------------------------------------------------

data Abs = Abs {- params -} [Ident] {- bindings -} [(Ident, AllocRegion, CExpr Abs)] (CExpr Abs)
  deriving Data

data Func = Func Type {- params -} [Ident] {- bindings -} [(Ident, AllocRegion, CExpr FuncRef)] (CExpr FuncRef)
  deriving (Data, Show)

data AbsEnv = AbsEnv
  { funcRefMap :: Map FuncRef Func
  , nextFuncRef :: Int
  } deriving Show

abstractUnsaturatedApps :: CExpr Abs -> Unique (CExpr Abs)
abstractUnsaturatedApps = transformM go
  where
    go :: CExpr Abs -> Unique (CExpr Abs)
    go e@(CIndexed [] (CApp t f args)) = case drop (length args) (paramTypes $ cexprType f) of
      -- Saturated, keep as is
      [] -> pure e
      -- Unsaturated, create closure
      remainingParams -> do
        argNames <- sequence [ fresh | _ <- args ]
        remainingParamNames <- sequence [ (,t) <$> fresh | t <- remainingParams ]

        let argBindings = [ (n, ALocal, arg) | (n, arg) <- zip argNames args ]
        let closureBody = CIndexed [] $ CApp t f $ mconcat
              [ [ CIndexed [] (CVar (cexprType a) n) | (n, a) <- zip argNames args ]
              , [ CIndexed [] (CVar pt mn) | (mn, pt) <- remainingParamNames ]
              ]

        pure $ CAbs (TAbs remainingParams t) $ Abs (map fst remainingParamNames) argBindings closureBody
    go ch = pure ch

gatherAbstractions :: CExpr Abs -> ST.State AbsEnv (CExpr FuncRef)
gatherAbstractions (CSel t choices selector) = do
  choices' <- traverse gatherAbstractions choices
  selector' <- gatherAbstractions selector
  pure $ CSel t choices' selector'
gatherAbstractions (CIndexed idxs expr) = do
  idxs' <- traverse (\(t, c) -> (t,) <$> gatherAbstractions c) idxs
  expr' <- gatherAbstractionsExpr expr
  pure $ CIndexed idxs' expr'
gatherAbstractions (CArr t choices) = do
  choices' <- traverse gatherAbstractions choices
  pure $ CArr t choices'
gatherAbstractions (CConst n) = pure $ CConst n
gatherAbstractions (COp t op a b) = do
  a' <- gatherAbstractions a
  b' <- gatherAbstractions b
  pure $ COp t op a' b'
gatherAbstractions (CAbs t (Abs params bindings body)) = do
  fr <- FuncRef <$> ST.gets (.nextFuncRef)
  bindings' <- sequence [ (n, region,) <$> gatherAbstractions b | (n, region, b) <- bindings ]
  body' <- gatherAbstractions body

  ST.modify $ \st -> st
    { nextFuncRef = st.nextFuncRef + 1
    , funcRefMap = M.insert fr (Func t params bindings' body') st.funcRefMap
    }

  pure $ CAbs t fr

gatherAbstractionsExpr :: CIndexable Abs -> ST.State AbsEnv (CIndexable FuncRef)
gatherAbstractionsExpr (CVar t ident) = pure $ CVar t ident
gatherAbstractionsExpr (CApp t f args) = do
  f' <- gatherAbstractions f
  args' <- traverse gatherAbstractions args
  pure $ CApp t f' args'
gatherAbstractionsExpr (CRec t delay param bindings body) = do
  body' <- gatherAbstractions body
  bindings' <- sequence [ (n, region,) <$> gatherAbstractions bbody | (n, region, bbody) <- bindings ]
  pure $ CRec t delay param bindings' body'

-- | Compute the free variables for each abstraction in the function map.
--
-- Free variables are variables that are referenced but not bound by parameters or bindings.
-- This includes both direct variable references (CVar) and transitive free variables from
-- nested closures (via SFuncRef).
--
-- The computation is recursive: when a function contains a closure (SFuncRef), that closure's
-- free variables are included in the parent function's free variables (unless they're bound
-- by the parent's parameters or bindings). This allows us to track which variables need to
-- be captured across multiple levels of nesting.
--
-- Example:
--   function outer(x) {
--     let y = 1;
--     return function middle(z) {
--       return function inner(w) {
--         return x + y + z + w;  // inner's free vars: {x, y, z}
--       }
--     }
--   }
--
-- Results:
--   - inner's free vars: {x, y, z}
--   - middle's free vars: {x, y} (includes inner's free vars minus middle's params/bindings)
--   - outer's free vars: {} (all variables are bound by outer)
gatherFreeVars :: Map FuncRef Func -> Map FuncRef (Set Ident)
gatherFreeVars funcRefMap = freeVarMap
  where
    freeVarMap :: Map FuncRef (Set Ident)
    freeVarMap = fmap go funcRefMap
      where
        go :: Func -> Set Ident
        go (Func _ params bindings body) = allVars bindings body \\ (S.fromList [ n | (n, _, _) <- bindings ] <> S.fromList params)

        allVars :: [(Ident, AllocRegion, CExpr FuncRef)] -> CExpr FuncRef -> Set Ident
        allVars bindings body = mconcat $ fmap mconcat
          [ [ S.fromList [ n | CVar @FuncRef _ n <- universeBi body ] ]
          , [ S.fromList [ n | (_, _, b) <- bindings, CVar @FuncRef _ n <- universeBi b ] ]

          -- Gather transient free vars (by lazily referencing freeVarMap; this works because no mutual recursion between bindings is allowed)
          , [ fvs | CAbs _ fr <- universeBi body, Just fvs <- [ M.lookup fr freeVarMap ] ]
          , [ fvs | (_, _, b) <- bindings, CAbs _ fr <- universeBi b, Just fvs <- [ M.lookup fr freeVarMap ] ]
          ]

--------------------------------------------------------------------------------

data GlobalsEnv = GlobalsEnv
  { substMap :: Map FuncRef (Map Ident Ident)
  , globals :: Map Ident Type
  }

instance Semigroup GlobalsEnv where GlobalsEnv a b <> GlobalsEnv a' b' = GlobalsEnv (a <> a') (b <> b')
instance Monoid GlobalsEnv where mempty = GlobalsEnv mempty mempty

-- | Transform abstractions to handle captured parameters by creating global bindings.
--
-- This function implements closure conversion for captured parameters. When a nested closure
-- references a parameter from an outer function, we need to make that parameter accessible
-- to the closure. Since the target language (WASM) doesn't support closures natively, we:
--
-- 1. Create a global binding for each captured parameter (e.g., _captured_0 = x)
-- 2. Mark any captured local bindings as global (they keep their original names)
-- 3. Build a substitution map for each closure, mapping original param names to global names
-- 4. Apply substitutions to each closure so it references the global bindings
--
-- Example transformation:
--   function outer(x, y) {
--     let z = 1;
--     return function inner(a) {
--       return x + z + a;  // inner captures param x and binding z
--     }
--   }
--
-- Becomes:
--   function outer(x, y) {
--     global _captured_0 = x;  // New global binding for captured param
--     global z = 1;             // Existing binding marked as global
--     return function inner(a) {
--       return _captured_0 + z + a;  // References substituted
--     }
--   }
--
-- The substitution map tracks: inner -> {x -> _captured_0}
-- Note that z doesn't need substitution since bindings keep their original names.
--
-- Returns:
--   - Updated function map with global bindings and substitutions applied
--   - GlobalsEnv containing the substitution map and global variable types
markCapturedBindings :: Map FuncRef (Set Ident) -> Map FuncRef Func -> Unique (Map FuncRef Func, GlobalsEnv)
markCapturedBindings freeVarMap funcRefMap = do
  (funcRefMapWithGlobalBindings, genv) <- W.runWriterT (traverse go funcRefMap)
  pure (M.mapWithKey (substituteVars genv.substMap) funcRefMapWithGlobalBindings, genv)
  where
    -- Process a single function to create global bindings for captured parameters
    go :: Func -> W.WriterT GlobalsEnv Unique Func
    go abs@(Func t params bindings body) = do
      -- Find all closures defined in this function and their free variables
      let freeVarsForClosure =
            [ (fr, fvs)
            | CAbs _ fr <- universeBi abs
            , Just fvs <- [ M.lookup fr freeVarMap ]
            ]
      -- Union of all free variables from nested closures
      let freeVars = mconcat (fmap snd freeVarsForClosure)

      -- Create fresh global names for each captured parameter
      capturedParams <- sequence
        [ (ptype, n,) <$> lift fresh
        | (ptype, n) <- zip (paramTypes t) params
        , S.member n freeVars
        ]

      -- Build substitution map: original param name -> fresh global name
      let paramSubsts = M.fromList [ (n, subst) | (_, n, subst) <- capturedParams ]
      
      -- Update bindings: mark captured bindings as global, add new global bindings for captured params
      let bindings' = mconcat
            [ [ if S.member n freeVars then (n, AGlobal, body) else (n, r, body)
              | (n, r, body) <- bindings
              ]
            , [ (subst, AGlobal, CIndexed [] (CVar t n)) | (t, n, subst) <- capturedParams ]
            ]
      
      -- Record substitutions and global types
      W.tell $ GlobalsEnv
        { substMap = M.fromListWith (<>)
            -- For each closure and each of its free variables that's a captured param,
            -- record the substitution that should be applied to that closure
            [ (fr, M.singleton fv subst)
            | (fr, fvs) <- freeVarsForClosure
            , fv <- S.toList fvs
            , Just subst <- [ M.lookup fv paramSubsts ]
            ]

        , globals = mconcat
            [ M.fromList [ (n, ptype) | (ptype, _, n) <- capturedParams ]
            , M.fromList [ (n, cexprType e) | (n, AGlobal, e) <- bindings' ]
            ] 
        }

      pure $ Func t params bindings' body

    -- Apply substitutions to a specific function based on its FuncRef
    substituteVars :: Map FuncRef (Map Ident Ident) -> FuncRef -> Func -> Func
    substituteVars frSubstMap fr a@(Func t params bindings body) = case M.lookup fr frSubstMap of
      Just substMap -> Func t params
        (fmap substBinding bindings)
        (transformBi substVar body)
        where
          substBinding (n, region, body)
            -- Don't substitute the RHS of captured param bindings (e.g., _captured_0 = x)
            -- We want to keep the original reference to the parameter
            | Just _ <- M.lookup n substMap = (n, region, body)
            | otherwise = (n, region, transformBi substVar body)

          substVar :: CIndexable FuncRef -> CIndexable FuncRef
          substVar (CVar t n) = CVar t (M.findWithDefault n n substMap)
          substVar e = e
      _ -> a

--------------------------------------------------------------------------------

-- NOTE: if bindings between two SAbs float collapse them into one
floatExpressions :: Map FuncRef Func -> Map FuncRef Func
floatExpressions = fmap go
  where
    go :: Func -> Func
    go (Func t params bindings body) = undefined

    isPure :: CExpr abs -> CExpr abs
    isPure = undefined

markPureExpressions :: Map FuncRef Func -> Map FuncRef Func
markPureExpressions = fmap go
  where
    go :: Func -> Func
    go (Func t params bindings body) = undefined

    isPure :: CExpr abs -> CExpr abs
    isPure = undefined

-- NEXT
-- * DONE mark captured bindings for storing in global
-- * DONE introduce global bindings for captured arguments, assign argument to them, replace reference to argument with ref to binding in closure
-- * codegen while maintaining focus/select lens
-- * alloc when calling
-- * delay lines (they must have configurable delay); must also be initialized with the initial value
-- * when choice do binary if/elses
-- ** fold the pure part of a computation into the if/else leaves, leaving the impure computations of all parts outside the if/else tree

--------------------------------------------------------------------------------

compile :: Map Ident (CExpr Abs) -> (Map Ident (CExpr FuncRef), Map FuncRef Func)
compile toplevelMap = runUnique $ do
  satMap <- traverse abstractUnsaturatedApps toplevelMap

  let (toplevelMap', env) = flip ST.runState (AbsEnv mempty 0) $ traverse gatherAbstractions satMap
  let freeVarMap = gatherFreeVars env.funcRefMap

  (funcRefMap, _) <- markCapturedBindings freeVarMap env.funcRefMap
  
  -- TODO
  let optimize = id

  pure (toplevelMap', optimize funcRefMap)

--------------------------------------------------------------------------------
-- Test expressions for markCapturedBindings

-- Test 1: Simple abstraction with no captures
testCExpr1 :: CExpr Abs
testCExpr1 = CAbs (TAbs [TNumber TI32] (TNumber TI32)) $ Abs
  [Ident "x"]
  [(Ident "x", ALocal, CConst (I32 0))]
  (CIndexed [] (CVar (TNumber TI32) (Ident "x")))

-- Test 2: Abstraction that captures a parameter in a nested abstraction
testCExpr2 :: CExpr Abs
testCExpr2 = CAbs (TAbs [TNumber TI32, TNumber TI32] (TNumber TI32)) $ Abs
  [Ident "x", Ident "y"]
  [(Ident "z", ALocal, CConst (I32 0))]
  (CAbs (TAbs [TNumber TI32] (TNumber TI32)) $ Abs
    [Ident "a"]
    [(Ident "b", ALocal, CConst (I32 1))]
    (COp (TNumber TI32) Add (CIndexed [] (CVar (TNumber TI32) (Ident "x"))) (CIndexed [] (CVar (TNumber TI32) (Ident "z")))))

-- Test 3: Abstraction with a binding that references a parameter
testCExpr3 :: CExpr Abs
testCExpr3 = CAbs (TAbs [TNumber TI32] (TNumber TI32)) $ Abs
  [Ident "x"]
  [ (Ident "x", ALocal, CConst (I32 5))
  , (Ident "y", ALocal, CIndexed [] (CVar (TNumber TI32) (Ident "x")))
  ]
  (CIndexed [] (CVar (TNumber TI32) (Ident "y")))

-- Test 4: Nested abstractions with multiple captures
testCExpr4 :: CExpr Abs
testCExpr4 = CAbs (TAbs [TNumber TI32, TNumber TI32] (TNumber TI32)) $ Abs
  [Ident "a", Ident "b"]
  [(Ident "bnd_a", ALocal, CConst (I32 1))]
  (CAbs (TAbs [TNumber TI32] (TNumber TI32)) $ Abs
    [Ident "c"]
    [ (Ident "bnd_b", ALocal, CIndexed [] (CVar (TNumber TI32) (Ident "bnd_a")))
    , (Ident "bnd_c", ALocal, CIndexed [] (CVar (TNumber TI32) (Ident "a")))
    ]
    (COp (TNumber TI32) Mul (CIndexed [] (CVar (TNumber TI32) (Ident "c"))) (CIndexed [] (CVar (TNumber TI32) (Ident "b")))))

-- Test 4: Nested abstractions with multiple captures
testCExpr4_2 :: CExpr Abs
testCExpr4_2 = CAbs (TAbs [TNumber TI32, TNumber TI32, TNumber TI32] (TNumber TI32)) $ Abs
  [Ident "a", Ident "b", Ident "z"]
  [(Ident "bnd_a", ALocal, CConst (I32 1))]
  (CAbs (TAbs [TNumber TI32] (TNumber TI32)) $ Abs
    [Ident "c"]
    [ (Ident "bnd_b", ALocal, CIndexed [] (CVar (TNumber TI32) (Ident "a")))
    , (Ident "bnd_c", ALocal, CIndexed [] (CVar (TNumber TI32) (Ident "z")))
    ]
    (CSel (TNumber TI32)
      [ (COp (TNumber TI32) Mul (CIndexed [] (CVar (TNumber TI32) (Ident "c"))) (CIndexed [] (CVar (TNumber TI32) (Ident "b"))))
      , (COp (TNumber TI32) Mul (CIndexed [] (CVar (TNumber TI32) (Ident "c"))) (CIndexed [] (CVar (TNumber TI32) (Ident "z"))))
      ] (COp (TNumber TI32) Mul (CIndexed [] (CVar (TNumber TI32) (Ident "bnd_a"))) (CIndexed [] (CVar (TNumber TI32) (Ident "z"))))))

testCExpr4_3 :: CExpr Abs
testCExpr4_3 = CAbs (TAbs [TNumber TI32, TNumber TI32, TNumber TI32] (TNumber TI32)) $ Abs
  [Ident "a", Ident "b", Ident "z"]
  [(Ident "bnd_a", ALocal, CConst (I32 1))]
  (CAbs (TAbs [TNumber TI32] (TNumber TI32)) $ Abs
    [Ident "c"]
    [ (Ident "bnd_b", ALocal, CIndexed [] (CVar (TNumber TI32) (Ident "a")))
    , (Ident "bnd_c", ALocal, CIndexed [] (CVar (TNumber TI32) (Ident "z")))
    ]
    (CSel (TArr (TNumber TI32) 3)
      [ (COp (TNumber TI32) Mul (CIndexed [] (CVar (TNumber TI32) (Ident "c"))) (CIndexed [] (CVar (TNumber TI32) (Ident "b"))))
      , (COp (TNumber TI32) Mul (CIndexed [] (CVar (TNumber TI32) (Ident "c"))) (CIndexed [] (CVar (TNumber TI32) (Ident "z"))))
      , (CSel (TArr (TNumber TI32) 3)
          [ (COp (TNumber TI32) Mul (CIndexed [] (CVar (TNumber TI32) (Ident "c"))) (CIndexed [] (CVar (TNumber TI32) (Ident "b"))))
          , (COp (TNumber TI32) Mul (CIndexed [] (CVar (TNumber TI32) (Ident "c"))) (CIndexed [] (CVar (TNumber TI32) (Ident "z"))))
          ] (CSel (TArr (TNumber TI32) 3)
                 [ (CConst $ I32 1)
                 , (COp (TNumber TI32) Mul (CIndexed [] (CVar (TNumber TI32) (Ident "c"))) (CIndexed [] (CVar (TNumber TI32) (Ident "z"))))
                 ] (CConst $ I32 0))) 
      ] (CConst $ I32 2)))

-- Test 5: Abstraction with free variable (not captured, just free)
testCExpr5 :: CExpr Abs
testCExpr5 = CAbs (TAbs [TNumber TI32] (TNumber TI32)) $ Abs
  [Ident "x"]
  [(Ident "x", ALocal, CConst (I32 0))]
  (COp (TNumber TI32) Add (CIndexed [] (CVar (TNumber TI32) (Ident "x"))) (CIndexed [] (CVar (TNumber TI32) (Ident "freeVar"))))

-- Test 6: Complex case with binding that captures and is itself captured
testCExpr6 :: CExpr Abs
testCExpr6 = CAbs (TAbs [TNumber TI32, TNumber TI32] (TNumber TI32)) $ Abs
  [Ident "x", Ident "y"]
  [ (Ident "x", ALocal, CConst (I32 10))
  , (Ident "helper", ALocal, CAbs (TAbs [TNumber TI32] (TNumber TI32)) $ Abs
      [Ident "z"]
      [(Ident "z", ALocal, CConst (I32 0))]
      (COp (TNumber TI32) Add (CIndexed [] (CVar (TNumber TI32) (Ident "x"))) (CIndexed [] (CVar (TNumber TI32) (Ident "z")))))
  ]
  (CAbs (TAbs [TNumber TI32] (TNumber TI32)) $ Abs
    [Ident "y"]
    [(Ident "y", ALocal, CConst (I32 20))]
    (CIndexed [] $ CApp (TNumber TI32) (CIndexed [] (CVar (TNumber TI32) (Ident "helper"))) [CIndexed [] (CVar (TNumber TI32) (Ident "y"))]))

testMark :: CExpr Abs -> (Map FuncRef Func, GlobalsEnv)
testMark e = runUnique $ do
  e' <- abstractUnsaturatedApps e
  let (e'', env) = ST.runState (gatherAbstractions e') (AbsEnv mempty 0)
  let freeVarMap = gatherFreeVars env.funcRefMap
  markCapturedBindings freeVarMap env.funcRefMap
