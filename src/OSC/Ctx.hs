{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}

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

data Type = TI32 | TF32 | TI64 | TF64 | TArr Type {- length -} Int | TAbs [Type] Type
  deriving (Data)

sizeOfType :: Type -> Int
sizeOfType TI32 = 4
sizeOfType TF32 = 4
sizeOfType TI64 = 8
sizeOfType TF64 = 8
sizeOfType (TArr t dim) = sizeOfType t * dim
sizeOfType (TAbs _ _) = sizeOfType TI32 -- TODO PLATFORM: funcref is I32

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
numberType (I32 _) = TI32
numberType (F32 _) = TF32
numberType (I64 _) = TI64
numberType (F64 _) = TF64

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
  | ERec Type {- delay -} Int {- must be of type abstraction -} Expr
  deriving Show

exprType :: Expr -> Type
exprType (EConst n) = numberType n
exprType (EOp t _ _ _) = t
exprType (EArr t _) = t
exprType (EVar t _) = t
exprType (EAbs t _ _ _) = t
exprType (EApp t _ _) = t
exprType (ESelect t _ _) = t
exprType (ERec t _ _) = t

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

-- TODO: optimization is performed on the Choice datatype

-- TODO: alignment in AllocM!

-- TODO: what happens if part of the return value is a capture?
-- this is basically return value ref propagation up the binding chain
-- the most recent returned binding (or argument) gets tagged with "write to return value ref"

newtype FuncRef = FuncRef Int deriving (Eq, Ord, Data, Show)

data AllocRegion = ALocal | AGlobal
  deriving (Show, Data)

data SExpr
  = SConst Number
  | SArr Type [Choice]
  | SOp Type Op Choice Choice

  | SVar Type Ident

  | SAbs Type {- params -} [Ident] {- bindings -} [(Ident, AllocRegion, Choice)] Choice
  | SApp Type Choice [Choice]

  | SRec Type {- delay -} Int {- must be of type abstraction -} Choice

  | SFuncRef Type FuncRef
  deriving Data

newtype Pureness = Pureness Bool
  deriving (Data, Show)

newtype CanFloat = CanFloat Bool
  deriving (Data, Show)

data Choice
  = CChoice Type [Choice] {- selector -} Choice
  | CExpr [(Type, Choice)] SExpr -- selection indices that flow into the inner expression
  deriving Data

choiceType :: Choice -> Type
choiceType (CChoice t _ _) = t
choiceType (CExpr idxs expr) = peelOffIndices (length idxs) (sexprType expr)
  where
    peelOffIndices :: Int -> Type -> Type
    peelOffIndices 0 t = t
    peelOffIndices n (TArr t _) = peelOffIndices (n - 1) t
    peelOffIndices _ t = error $ "choiceType: cannot peel " <> show (length idxs) <> " indices from type " <> show t <> " (this is a bug)"

sexprType :: SExpr -> Type
sexprType (SConst n) = numberType n
sexprType (SArr t _) = t
sexprType (SOp t _ _ _) = t
sexprType (SVar t _) = t
sexprType (SAbs t _ _ _) = t
sexprType (SApp t _ _) = t
sexprType (SRec t _ _) = t
sexprType (SFuncRef t _) = t

--------------------------------------------------------------------------------

instance Show SExpr where
  show (SConst n) = show n
  show (SArr t cs) = "[" <> showType t <> ": " <> intercalate ", " (map show cs) <> "]"
  show (SOp _ op a b) = "(" <> show a <> " " <> showOp op <> " " <> show b <> ")"
  show (SVar _ (Ident n)) = n
  show (SAbs t params bs body) = 
    "λ" <> showParams params <> " : " <> showType t <> " " <> showBindings bs <> " = " <> show body
    where
      showParams [] = "()"
      showParams ps = "(" <> intercalate ", " (map (\(Ident n) -> n) ps) <> ")"
      showBindings [] = ""
      showBindings bindings = "{ " <> intercalate "; " (map showBinding bindings) <> " }"
      showBinding (Ident n, region, expr) = 
        n <> "@" <> showRegion region <> " = " <> show expr
      showRegion ALocal = "local"
      showRegion AGlobal = "global"
  show (SApp _ f a) = show f <> "(" <> show a <> ")"
  show (SRec t delay body) = "rec[" <> showType t <> ", delay=" <> show delay <> "](" <> show body <> ")"
  show (SFuncRef _ (FuncRef n)) = "funcref#" <> show n

instance Show Choice where
  show (CChoice t cs idx) = 
    "choice[" <> showType t <> "](" <> intercalate " | " (map show cs) <> ")[" <> show idx <> "]"
  show (CExpr [] expr) = show expr
  show (CExpr idxs expr) = 
    show expr <> " @ [" <> intercalate ", " (map showIdxPair idxs) <> "]"
    where
      showIdxPair (t, idx) = showType t <> "[" <> show idx <> "]"

instance Show Type where
  show = showType

showType :: Type -> String
showType TI32 = "i32"
showType TF32 = "f32"
showType TI64 = "i64"
showType TF64 = "f64"
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

toC :: Monad m => SExpr -> StackM (Type, Expr) m Choice
toC e = do
  idxs <- ST.get
  pure $ CExpr (map (second toChoice) idxs) e

choiceTree :: Monad m => Expr -> StackM (Type, Expr) m Choice
choiceTree (EConst n) = toC (SConst n)
choiceTree (EOp t op a b) = toC (SOp t op (toChoice a) (toChoice b))
choiceTree (EVar t n) = toC (SVar t n)
choiceTree (EApp t f as) = toC (SApp t (toChoice f) (fmap toChoice as))
choiceTree (EAbs t params bs e) = toC (SAbs t params (map (second toChoice) [ (n, ALocal, b) | (n, b) <- bs ]) (toChoice e))
choiceTree (ERec t d e) = toC (SRec t d (toChoice e))
choiceTree (EArr t es) = do
  s <- pop
  case s of
    Just (t, idx) -> do
      es' <- traverse choiceTree es
      push (t, idx)
      pure $ CChoice t es' (toChoice idx)
    Nothing -> pure $ CExpr [] (SArr t $ map toChoice es)
choiceTree (ESelect t e idx) = do
  push (t, idx)
  c <- choiceTree e
  _ <- pop
  pure c

--------------------------------------------------------------------------------

elimConstIndices :: Choice -> Choice
elimConstIndices = transform go
  where
    go :: Choice -> Choice

    -- Eliminate constant index selections by directly selecting the choice
    -- It's ok to prune impure expressions here (since the index is constant those expressions will never be accessible)
    go (CChoice _ chs (CExpr _ (SConst (I32 idx)))) = chs !! idx
    go (CChoice _ chs (CExpr _ (SConst (I64 idx)))) = chs !! idx

    -- Keep everything else as-is
    go ch = ch

optimize :: Choice -> Choice
optimize = elimConstIndices

toChoice :: Expr -> Choice
toChoice = optimize . flip ST.evalState [] . choiceTree

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

data Abs = Abs Type {- params -} [Ident] {- bindings -} [(Ident, AllocRegion, Choice)] Choice
  deriving Data

instance Show Abs where
  show (Abs t params bs e) = show (SAbs t params bs e)

data AbsEnv = AbsEnv
  { funcRefMap :: Map FuncRef Abs
  , nextFuncRef :: Int
  } deriving Show

abstractUnsaturatedApps :: Choice -> Unique Choice
abstractUnsaturatedApps = transformBiM go
  where
    go :: SExpr -> Unique SExpr
    go e@(SApp t f args) = case drop (length args) (paramTypes $ choiceType f) of
      -- Saturated, keep as is
      [] -> pure e
      -- Unsaturated, create closure
      remainingParams -> do
        argNames <- sequence [ fresh | _ <- args ]
        remainingParamNames <- sequence [ (,t) <$> fresh | t <- remainingParams ]

        let argBindings = [ (n, ALocal, arg) | (n, arg) <- zip argNames args ]
        let closureBody = CExpr [] $ SApp t f $ mconcat
              [ [ CExpr [] (SVar (choiceType a) n) | (n, a) <- zip argNames args ]
              , [ CExpr [] (SVar pt mn) | (mn, pt) <- remainingParamNames ]
              ]

        pure $ SAbs (TAbs remainingParams t) (map fst remainingParamNames) argBindings closureBody
    go e = pure e

gatherAbstractions :: Choice -> (Choice, AbsEnv)
gatherAbstractions = flip ST.runState (AbsEnv mempty 0) . transformBiM processAbstraction
  where
    processAbstraction :: SExpr -> ST.State AbsEnv SExpr
    processAbstraction (SAbs t params bs body) = do
      fr <- FuncRef <$> ST.gets (.nextFuncRef)

      ST.modify $ \st -> st
        { nextFuncRef = st.nextFuncRef + 1
        , funcRefMap = M.insert fr (Abs t params bs body) st.funcRefMap
        }

      pure $ SFuncRef t fr
    processAbstraction e = pure e

-- | Compute the free variables for each abstraction in the function map.
--
-- Free variables are variables that are referenced but not bound by parameters or bindings.
-- This includes both direct variable references (SVar) and transitive free variables from
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
gatherFreeVars :: Map FuncRef Abs -> Map FuncRef (Set Ident)
gatherFreeVars funcRefMap = freeVarMap
  where
    freeVarMap :: Map FuncRef (Set Ident)
    freeVarMap = fmap go funcRefMap
      where
        go :: Abs -> Set Ident
        go (Abs _ params bindings body) = allVars bindings body \\ (S.fromList [ n | (n, _, _) <- bindings ] <> S.fromList params)

        allVars :: [(Ident, AllocRegion, Choice)] -> Choice -> Set Ident
        allVars bindings body = mconcat $ fmap mconcat
          [ [ S.fromList [ n | SVar _ n <- universeBi body ] ]
          , [ S.fromList [ n | (_, _, b) <- bindings, SVar _ n <- universeBi b ] ]

          -- Gather transient free vars (by lazily referencing freeVarMap; this works because no mutual recursion between bindings is allowed)
          , [ fvs | SFuncRef _ fr <- universeBi body, Just fvs <- [ M.lookup fr freeVarMap ] ]
          , [ fvs | (_, _, b) <- bindings, SFuncRef _ fr <- universeBi b, Just fvs <- [ M.lookup fr freeVarMap ] ]
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
markCapturedBindings :: Map FuncRef (Set Ident) -> Map FuncRef Abs -> Unique (Map FuncRef Abs, GlobalsEnv)
markCapturedBindings freeVarMap funcRefMap = do
  (funcRefMapWithGlobalBindings, genv) <- W.runWriterT (traverse go funcRefMap)
  pure (M.mapWithKey (substituteVars genv.substMap) funcRefMapWithGlobalBindings, genv)
  where
    -- Process a single function to create global bindings for captured parameters
    go :: Abs -> W.WriterT GlobalsEnv Unique Abs
    go abs@(Abs t params bindings body) = do
      -- Find all closures defined in this function and their free variables
      let freeVarsForClosure =
            [ (fr, fvs)
            | SFuncRef _ fr <- universeBi abs
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
            , [ (subst, AGlobal, CExpr [] (SVar t n)) | (t, n, subst) <- capturedParams ]
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
            , M.fromList [ (n, choiceType e) | (n, AGlobal, e) <- bindings' ]
            ] 
        }

      pure $ Abs t params bindings' body

    -- Apply substitutions to a specific function based on its FuncRef
    substituteVars :: Map FuncRef (Map Ident Ident) -> FuncRef -> Abs -> Abs
    substituteVars frSubstMap fr a@(Abs t params bindings body) = case M.lookup fr frSubstMap of
      Just substMap -> Abs t params
        (fmap substBinding bindings)
        (transformBi substVar body)
        where
          substBinding (n, region, body)
            -- Don't substitute the RHS of captured param bindings (e.g., _captured_0 = x)
            -- We want to keep the original reference to the parameter
            | Just _ <- M.lookup n substMap = (n, region, body)
            | otherwise = (n, region, transformBi substVar body)

          substVar (SVar t n) = SVar t (M.findWithDefault n n substMap)
          substVar e = e
      _ -> a

--------------------------------------------------------------------------------

-- NOTE: if bindings between two SAbs float collapse them into one
floatExpressions :: Map FuncRef Abs -> Map FuncRef Abs
floatExpressions = fmap go
  where
    go :: Abs -> Abs
    go (Abs t params bindings body) = undefined

    isPure :: Choice -> Choice
    isPure = undefined

markPureExpressions :: Map FuncRef Abs -> Map FuncRef Abs
markPureExpressions = fmap go
  where
    go :: Abs -> Abs
    go (Abs t params bindings body) = undefined

    isPure :: Choice -> Choice
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
-- Test expressions for markCapturedBindings

-- Test 1: Simple abstraction with no captures
testChoice1 :: Choice
testChoice1 = CExpr [] $ SAbs
  (TAbs [TI32] TI32)
  [Ident "x"]
  [(Ident "x", ALocal, CExpr [] (SConst (I32 0)))]
  (CExpr [] (SVar TI32 (Ident "x")))

-- Test 2: Abstraction that captures a parameter in a nested abstraction
testChoice2 :: Choice
testChoice2 = CExpr [] $ SAbs
  (TAbs [TI32, TI32] TI32)
  [Ident "x", Ident "y"]
  [(Ident "z", ALocal, CExpr [] (SConst (I32 0)))]
  (CExpr [] $ SAbs
    (TAbs [TI32] TI32)
    [Ident "a"]
    [(Ident "b", ALocal, CExpr [] (SConst (I32 1)))]
    (CExpr [] $ SOp TI32 Add (CExpr [] (SVar TI32 (Ident "x"))) (CExpr [] (SVar TI32 (Ident "z")))))

-- Test 3: Abstraction with a binding that references a parameter
testChoice3 :: Choice
testChoice3 = CExpr [] $ SAbs
  (TAbs [TI32] TI32)
  [Ident "x"]
  [ (Ident "x", ALocal, CExpr [] (SConst (I32 5)))
  , (Ident "y", ALocal, CExpr [] (SVar TI32 (Ident "x")))
  ]
  (CExpr [] (SVar TI32 (Ident "y")))

-- Test 4: Nested abstractions with multiple captures
testChoice4 :: Choice
testChoice4 = CExpr [] $ SAbs
  (TAbs [TI32, TI32] TI32)
  [Ident "a", Ident "b"]
  [(Ident "bnd_a", ALocal, CExpr [] (SConst (I32 1)))]
  (CExpr [] $ SAbs
    (TAbs [TI32] TI32)
    [Ident "c"]
    [ (Ident "bnd_b", ALocal, CExpr [] (SVar TI32 (Ident "bnd_a")))
    , (Ident "bnd_c", ALocal, CExpr [] (SVar TI32 (Ident "a")))
    ]
    (CExpr [] $ SOp TI32 Mul (CExpr [] (SVar TI32 (Ident "c"))) (CExpr [] (SVar TI32 (Ident "b")))))

-- Test 4: Nested abstractions with multiple captures
testChoice4_2 :: Choice
testChoice4_2 = CExpr [] $ SAbs
  (TAbs [TI32, TI32, TI32] TI32)
  [Ident "a", Ident "b", Ident "z"]
  [(Ident "bnd_a", ALocal, CExpr [] (SConst (I32 1)))]
  (CExpr [] $ SAbs
    (TAbs [TI32] TI32)
    [Ident "c"]
    [ (Ident "bnd_b", ALocal, CExpr [] (SVar TI32 (Ident "a")))
    , (Ident "bnd_c", ALocal, CExpr [] (SVar TI32 (Ident "z")))
    ]
    (CChoice TI32
      [ (CExpr [] $ SOp TI32 Mul (CExpr [] (SVar TI32 (Ident "c"))) (CExpr [] (SVar TI32 (Ident "b"))))
      , (CExpr [] $ SOp TI32 Mul (CExpr [] (SVar TI32 (Ident "c"))) (CExpr [] (SVar TI32 (Ident "z"))))
      ] (CExpr [] $ SOp TI32 Mul (CExpr [] (SVar TI32 (Ident "bnd_a"))) (CExpr [] (SVar TI32 (Ident "z"))))))

testChoice4_3 :: Choice
testChoice4_3 = CExpr [] $ SAbs
  (TAbs [TI32, TI32, TI32] TI32)
  [Ident "a", Ident "b", Ident "z"]
  [(Ident "bnd_a", ALocal, CExpr [] (SConst (I32 1)))]
  (CExpr [] $ SAbs
    (TAbs [TI32] TI32)
    [Ident "c"]
    [ (Ident "bnd_b", ALocal, CExpr [] (SVar TI32 (Ident "a")))
    , (Ident "bnd_c", ALocal, CExpr [] (SVar TI32 (Ident "z")))
    ]
    (CChoice (TArr TI32 3)
      [ (CExpr [] $ SOp TI32 Mul (CExpr [] (SVar TI32 (Ident "c"))) (CExpr [] (SVar TI32 (Ident "b"))))
      , (CExpr [] $ SOp TI32 Mul (CExpr [] (SVar TI32 (Ident "c"))) (CExpr [] (SVar TI32 (Ident "z"))))
      , (CChoice (TArr TI32 3)
          [ (CExpr [] $ SOp TI32 Mul (CExpr [] (SVar TI32 (Ident "c"))) (CExpr [] (SVar TI32 (Ident "b"))))
          , (CExpr [] $ SOp TI32 Mul (CExpr [] (SVar TI32 (Ident "c"))) (CExpr [] (SVar TI32 (Ident "z"))))
          ] (CChoice (TArr TI32 3)
                 [ (CExpr [] $ SConst $ I32 1)
                 , (CExpr [] $ SOp TI32 Mul (CExpr [] (SVar TI32 (Ident "c"))) (CExpr [] (SVar TI32 (Ident "z"))))
                 ] (CExpr [] $ SConst $ I32 0))) 
      ] (CExpr [] $ SConst $ I32 2)))

-- Test 5: Abstraction with free variable (not captured, just free)
testChoice5 :: Choice
testChoice5 = CExpr [] $ SAbs
  (TAbs [TI32] TI32)
  [Ident "x"]
  [(Ident "x", ALocal, CExpr [] (SConst (I32 0)))]
  (CExpr [] $ SOp TI32 Add (CExpr [] (SVar TI32 (Ident "x"))) (CExpr [] (SVar TI32 (Ident "freeVar"))))

-- Test 6: Complex case with binding that captures and is itself captured
testChoice6 :: Choice
testChoice6 = CExpr [] $ SAbs
  (TAbs [TI32, TI32] TI32)
  [Ident "x", Ident "y"]
  [ (Ident "x", ALocal, CExpr [] (SConst (I32 10)))
  , (Ident "helper", ALocal, CExpr [] $ SAbs
      (TAbs [TI32] TI32)
      [Ident "z"]
      [(Ident "z", ALocal, CExpr [] (SConst (I32 0)))]
      (CExpr [] $ SOp TI32 Add (CExpr [] (SVar TI32 (Ident "x"))) (CExpr [] (SVar TI32 (Ident "z")))))
  ]
  (CExpr [] $ SAbs
    (TAbs [TI32] TI32)
    [Ident "y"]
    [(Ident "y", ALocal, CExpr [] (SConst (I32 20)))]
    (CExpr [] $ SApp TI32 (CExpr [] (SVar TI32 (Ident "helper"))) [CExpr [] (SVar TI32 (Ident "y"))]))

testMark :: Choice -> (Map FuncRef Abs, GlobalsEnv)
testMark e = runUnique $ do
  e' <- abstractUnsaturatedApps e
  let (e'', env) = gatherAbstractions e'
  let freeVarMap = gatherFreeVars env.funcRefMap
  markCapturedBindings freeVarMap env.funcRefMap
