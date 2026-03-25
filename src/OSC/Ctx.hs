{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}

module OSC.Ctx where

import Data.Bifunctor (second)
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

data Type = TI32 | TF32 | TI64 | TF64 | TArr Type {- length -} Int | TAbs [(Maybe Ident, Type)] Type
  deriving (Data)

sizeOfType :: Type -> Int
sizeOfType TI32 = 4
sizeOfType TF32 = 4
sizeOfType TI64 = 8
sizeOfType TF64 = 8
sizeOfType (TArr t dim) = sizeOfType t * dim
sizeOfType (TAbs _ _) = 4 -- funcref is an integer

returnType :: Type -> Type
returnType t@(TArr _ _) = t
returnType (TAbs _ t) = t
returnType t = t

peelType :: Type -> Type
peelType (TArr t _) = t
peelType (TAbs _ _) = error "peelType: abstraction"
peelType t = error $ "peelType: " <> show t

paramTypes :: Type -> [(Maybe Ident, Type)]
paramTypes (TArr _ _) = []
paramTypes (TAbs params _) = params
paramTypes _ = []

namedParamTypes :: Type -> [(Ident, Type)]
namedParamTypes (TArr _ _) = []
namedParamTypes (TAbs params _) = fmap p params
  where
    p (Just n, t) = (n, t)
    p (Nothing, _) = error "namedParamTypes: unnamed param (this is a bug)"
namedParamTypes _ = []

data Number = I32 Int | I64 Int | F32 Float | F64 Double
  deriving (Show, Data)

numberType :: Number -> Type
numberType (I32 _) = TI32
numberType (F32 _) = TF32
numberType (I64 _) = TI64
numberType (F64 _) = TF64

data Ident = Ident String
  deriving (Eq, Ord, Data, Show)

data Op = Add | Sub | Mul | Div | Mod | And | Or | Xor | Shl | Shr | Eq | Gt | Lt | GEt | LEt
  deriving (Data, Show)

data Expr
  = EConst Number
  | EOp Type Op Expr Expr -- both args and the result are simple types
  | EArr Type [Expr]

  | EVar Type Ident

  | EAbs Type {- bindings -} [(Ident, Expr)] {- body -} Expr
  | EApp Type Expr [Expr]

  | ESelect Type Expr {- selector -} Expr
  | ERec Type {- delay -} Int Ident {- init value -} Expr {- body -} Expr
  deriving Show

exprType :: Expr -> Type
exprType (EConst n) = numberType n
exprType (EOp t _ _ _) = t
exprType (EArr t _) = t
exprType (EVar t _) = t
exprType (EAbs t _ _) = t
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
  | SVarNS Type Ident -- shouldn't be substituted

  | SAbs Type {- bindings -} [(Ident, AllocRegion, Choice)] Choice
  | SApp Type Choice [Choice]

  | SFuncRef Type FuncRef
  deriving Data

newtype Pureness = Pureness Bool
  deriving (Data, Show)

newtype CanFloat = CanFloat Bool
  deriving (Data, Show)

data Choice
  = CChoice Type [Choice] {- selector -} Choice
  | CExpr [(Type, Choice)] SExpr -- selection indices that flow into the inner expression
  | CRec Type {- delay -} Int Ident {- init value -} Choice Choice
  deriving Data

choiceType :: Choice -> Type
choiceType (CChoice t _ _) = t
choiceType (CRec t _ _ _ _) = t
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
sexprType (SVarNS t _) = t
sexprType (SAbs t _ _) = t
sexprType (SApp t _ _) = t
sexprType (SFuncRef t _) = t

--------------------------------------------------------------------------------

instance Show SExpr where
  show (SConst n) = show n
  show (SArr t cs) = "[" <> showType t <> ": " <> intercalate ", " (map show cs) <> "]"
  show (SOp _ op a b) = "(" <> show a <> " " <> showOp op <> " " <> show b <> ")"
  show (SVar _ (Ident n)) = n
  show (SVarNS _ (Ident n)) = n
  show (SAbs t bs body) = 
    "λ" <> showType t <> " " <> showBindings bs <> " = " <> show body
    where
      showBindings [] = ""
      showBindings bindings = "{ " <> intercalate "; " (map showBinding bindings) <> " }"
      showBinding (Ident n, region, expr) = 
        n <> "@" <> showRegion region <> " = " <> show expr
      showRegion ALocal = "local"
      showRegion AGlobal = "global"
  show (SApp _ f a) = show f <> "(" <> show a <> ")"
  show (SFuncRef _ (FuncRef n)) = "funcref#" <> show n

instance Show Choice where
  show (CChoice t cs idx) = 
    "choice[" <> showType t <> "](" <> intercalate " | " (map show cs) <> ")[" <> show idx <> "]"
  show (CExpr [] expr) = show expr
  show (CExpr idxs expr) = 
    show expr <> " @ [" <> intercalate ", " (map showIdxPair idxs) <> "]"
    where
      showIdxPair (t, idx) = showType t <> "[" <> show idx <> "]"
  show (CRec t n (Ident d) ini body) = 
    "rec[" <> showType t <> ", " <> show n <> "] |" <> d <> " = " <> show ini <> "| -> " <> show body

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
  "(" <> intercalate ", " (map showParam params) <> ") -> " <> showType retType
  where
    showParam (Nothing, t) = showType t
    showParam (Just (Ident n), t) = n <> ":" <> showType t

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
showOp Eq = "=="
showOp Gt = ">"
showOp Lt = "<"
showOp GEt = ">="
showOp LEt = "<="

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
choiceTree (EAbs t bs e) = toC (SAbs t (map (second toChoice) [ (n, ALocal, b) | (n, b) <- bs ]) (toChoice e))
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
choiceTree (ERec t n d i e) = CRec t n d <$> choiceTree i <*> choiceTree e

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

data Abs = Abs Type {- bindings -} [(Ident, AllocRegion, Choice)] Choice
  deriving Data

instance Show Abs where
  show (Abs t bs e) = show (SAbs t bs e)

data AbsEnv = AbsEnv
  { funcRefMap :: Map FuncRef Abs
  , nextFuncRef :: Int
  } deriving Show

gatherAbstractions :: Choice -> Unique (Choice, AbsEnv)
gatherAbstractions ch = do
  ch' <- transformBiM abstractUnsaturatedApps ch
  ST.lift $ flip ST.runStateT (AbsEnv mempty 0) $ transformBiM processSAbs ch'
  where
    abstractUnsaturatedApps :: SExpr -> Unique SExpr
    abstractUnsaturatedApps e@(SApp t f as) = case drop (length as) (paramTypes $ choiceType f) of
      -- Saturated, keep as is
      [] -> pure e
      -- Unsaturated, create closure
      remainingParams -> do
        argNames <- sequence [ fresh | _ <- as ]
        pure $ SAbs (TAbs remainingParams t) argBindings closureBody
        where
          argBindings = [ (n, ALocal, arg) | (n, arg) <- zip argNames as ]
          argIdents = [ n | (n, _, _) <- argBindings ]
          
          closureBody = CExpr [] $ SApp t f 
            ([ CExpr [] (SVar (getArgType n argBindings) n) | n <- argIdents ]
             <> [ CExpr [] (SVar pt (maybe (Ident "_") id mn)) | (mn, pt) <- remainingParams ])
          
          getArgType n bindings = case lookup n [ (i, choiceType c) | (i, _, c) <- bindings ] of
            Just t' -> t'
            Nothing -> error "abstractUnsaturatedApps: argument not found in bindings"
    abstractUnsaturatedApps e = pure e

    processSAbs :: SExpr -> ST.StateT AbsEnv Unique SExpr
    processSAbs (SAbs t bs body) = do
      fr <- FuncRef <$> ST.gets (.nextFuncRef)

      ST.modify $ \st -> st
        { nextFuncRef = st.nextFuncRef + 1
        , funcRefMap = M.insert fr (Abs t bs body) st.funcRefMap
        }

      pure $ SFuncRef t fr
    processSAbs e = pure e

gatherFreeVars :: Map FuncRef Abs -> Map FuncRef (Set Ident)
gatherFreeVars funcRefMap = freeVarMap
  where
    freeVarMap :: Map FuncRef (Set Ident)
    freeVarMap = fmap go funcRefMap
      where
        go :: Abs -> Set Ident
        go (Abs t bindings body) = allVars bindings body \\ (S.fromList [ n | (n, _, _) <- bindings ] <> S.fromList (fmap fst $ namedParamTypes t))

        allVars :: [(Ident, AllocRegion, Choice)] -> Choice -> Set Ident
        allVars bindings body = mconcat $ fmap mconcat
          [ [ S.fromList [ n | SVar _ n <- universeBi body ] ]
          , [ S.fromList [ n | (_, _, b) <- bindings, SVar _ n <- universeBi b ] ]

          -- Gather transient free vars (by lazily referencing freeVarMap; this works because no mutual recursion between bindings is allowed)
          , [ fvs | SFuncRef _ fr <- universeBi body, Just fvs <- [ M.lookup fr freeVarMap ] ]
          , [ fvs | (_, _, b) <- bindings, SFuncRef _ fr <- universeBi b, Just fvs <- [ M.lookup fr freeVarMap ] ]
          ]

markCapturedBindings :: Map FuncRef (Set Ident) -> Map FuncRef Abs -> Unique (Map FuncRef Abs, Map Ident Ident)
markCapturedBindings freeVarMap funcRefMap = do
  (funcRefMapWithGlobalBindings, substMap) <- W.runWriterT (traverse go funcRefMap)
  pure ( fmap (transformBi (substituteVars substMap)) funcRefMapWithGlobalBindings
       , substMap
       )

  where

    go :: Abs -> W.WriterT (Map Ident Ident) Unique Abs
    go abs@(Abs t bindings body) = do
      capturedParams <- sequence
        [ (t, n,) <$> fresh
        | (n, _) <- namedParamTypes t
        , S.member n fvs
        ]
      
      W.tell $ M.fromList [ (o, n) | (_, o, n) <- capturedParams ]

      pure $ Abs t (bindings' capturedParams) body
      where
        fvs = transientFreeVars abs

        bindings' capturedParams = mconcat
          [ [ if S.member n fvs then (n, AGlobal, body) else b
            | b@(n, _, body) <- bindings
            ]
          , [ (n, AGlobal, CExpr [] (SVarNS t o)) | (t, o, n) <- capturedParams ] 
          ]

    transientFreeVars :: Abs -> Set Ident
    transientFreeVars abs = mconcat
      [ fvs
      | SFuncRef _ fr <- universeBi abs
      , Just fvs <- [ M.lookup fr freeVarMap ]
      ]

    -- Substitute variable references using uniplate
    substituteVars :: Map Ident Ident -> Choice -> Choice
    substituteVars subst = transformBi substVar
      where
        substVar (SVar t n) = SVar t (M.findWithDefault n n subst)
        substVar e = e

-- TODO: if bindings between two SAbs float collapse them into one
floatExpressions :: Map FuncRef Abs -> Map FuncRef Abs
floatExpressions = fmap go
  where
    go :: Abs -> Abs
    go (Abs t bindings body) = undefined

    isPure :: Choice -> Choice
    isPure = undefined

markPureExpressions :: Map FuncRef Abs -> Map FuncRef Abs
markPureExpressions = fmap go
  where
    go :: Abs -> Abs
    go (Abs t bindings body) = undefined

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
  (TAbs [(Just (Ident "x"), TI32)] TI32)
  [(Ident "x", ALocal, CExpr [] (SConst (I32 0)))]
  (CExpr [] (SVar TI32 (Ident "x")))

-- Test 2: Abstraction that captures a parameter in a nested abstraction
testChoice2 :: Choice
testChoice2 = CExpr [] $ SAbs
  (TAbs [(Just (Ident "x"), TI32), (Just (Ident "y"), TI32)] TI32)
  [(Ident "z", ALocal, CExpr [] (SConst (I32 0)))]
  (CExpr [] $ SAbs
    (TAbs [(Just (Ident "a"), TI32)] TI32)
    [(Ident "b", ALocal, CExpr [] (SConst (I32 1)))]
    (CExpr [] $ SOp TI32 Add (CExpr [] (SVar TI32 (Ident "x"))) (CExpr [] (SVar TI32 (Ident "z")))))

-- Test 3: Abstraction with a binding that references a parameter
testChoice3 :: Choice
testChoice3 = CExpr [] $ SAbs
  (TAbs [(Just (Ident "x"), TI32)] TI32)
  [ (Ident "x", ALocal, CExpr [] (SConst (I32 5)))
  , (Ident "y", ALocal, CExpr [] (SVar TI32 (Ident "x")))
  ]
  (CExpr [] (SVar TI32 (Ident "y")))

-- Test 4: Nested abstractions with multiple captures
testChoice4 :: Choice
testChoice4 = CExpr [] $ SAbs
  (TAbs [(Just (Ident "a"), TI32), (Just (Ident "b"), TI32)] TI32)
  [(Ident "bnd_a", ALocal, CExpr [] (SConst (I32 1)))]
  (CExpr [] $ SAbs
    (TAbs [(Just (Ident "c"), TI32)] TI32)
    [ (Ident "bnd_b", ALocal, CExpr [] (SVar TI32 (Ident "bnd_a")))
    , (Ident "bnd_c", ALocal, CExpr [] (SVar TI32 (Ident "a")))
    ]
    (CExpr [] $ SOp TI32 Mul (CExpr [] (SVar TI32 (Ident "c"))) (CExpr [] (SVar TI32 (Ident "b")))))

-- Test 4: Nested abstractions with multiple captures
testChoice4_2 :: Choice
testChoice4_2 = CExpr [] $ SAbs
  (TAbs [(Just (Ident "a"), TI32), (Just (Ident "b"), TI32), (Just (Ident "z"), TI32)] TI32)
  [(Ident "bnd_a", ALocal, CExpr [] (SConst (I32 1)))]
  (CExpr [] $ SAbs
    (TAbs [(Just (Ident "c"), TI32)] TI32)
    [ (Ident "bnd_b", ALocal, CExpr [] (SVar TI32 (Ident "a")))
    , (Ident "bnd_c", ALocal, CExpr [] (SVar TI32 (Ident "z")))
    ]
    (CChoice TI32
      [ (CExpr [] $ SOp TI32 Mul (CExpr [] (SVar TI32 (Ident "c"))) (CExpr [] (SVar TI32 (Ident "b"))))
      , (CExpr [] $ SOp TI32 Mul (CExpr [] (SVar TI32 (Ident "c"))) (CExpr [] (SVar TI32 (Ident "z"))))
      ] (CExpr [] $ SOp TI32 Mul (CExpr [] (SVar TI32 (Ident "bnd_a"))) (CExpr [] (SVar TI32 (Ident "z"))))))

testChoice4_3 :: Choice
testChoice4_3 = CExpr [] $ SAbs
  (TAbs [(Just (Ident "a"), TI32), (Just (Ident "b"), TI32), (Just (Ident "z"), TI32)] TI32)
  [(Ident "bnd_a", ALocal, CExpr [] (SConst (I32 1)))]
  (CExpr [] $ SAbs
    (TAbs [(Just (Ident "c"), TI32)] TI32)
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
  (TAbs [(Just (Ident "x"), TI32)] TI32)
  [(Ident "x", ALocal, CExpr [] (SConst (I32 0)))]
  (CExpr [] $ SOp TI32 Add (CExpr [] (SVar TI32 (Ident "x"))) (CExpr [] (SVar TI32 (Ident "freeVar"))))

-- Test 6: Complex case with binding that captures and is itself captured
testChoice6 :: Choice
testChoice6 = CExpr [] $ SAbs
  (TAbs [(Just (Ident "x"), TI32), (Just (Ident "y"), TI32)] TI32)
  [ (Ident "x", ALocal, CExpr [] (SConst (I32 10)))
  , (Ident "helper", ALocal, CExpr [] $ SAbs
      (TAbs [(Just (Ident "z"), TI32)] TI32)
      [(Ident "z", ALocal, CExpr [] (SConst (I32 0)))]
      (CExpr [] $ SOp TI32 Add (CExpr [] (SVar TI32 (Ident "x"))) (CExpr [] (SVar TI32 (Ident "z")))))
  ]
  (CExpr [] $ SAbs
    (TAbs [(Just (Ident "y"), TI32)] TI32)
    [(Ident "y", ALocal, CExpr [] (SConst (I32 20)))]
    (CExpr [] $ SApp TI32 (CExpr [] (SVar TI32 (Ident "helper"))) [CExpr [] (SVar TI32 (Ident "y"))]))

testMark :: Choice -> (Map FuncRef Abs, Map Ident Ident)
testMark ch = runUnique $ do
  (ch', env) <- gatherAbstractions ch
  let freeVarMap = gatherFreeVars env.funcRefMap
  markCapturedBindings freeVarMap env.funcRefMap
