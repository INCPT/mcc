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

data Type = TNumber | TArr Type {- length -} Int | TAbs (Maybe Ident) Type Type
  deriving (Data)

sizeOfType :: Type -> Int
sizeOfType TNumber = 4
sizeOfType (TArr t dim) = sizeOfType t * dim
sizeOfType (TAbs _ _ _) = 4 -- funcref is an integer

returnType :: Type -> Type
returnType TNumber = TNumber
returnType t@(TArr _ _) = t
returnType (TAbs _ _ t) = t

peelType :: Type -> Type
peelType (TArr t _) = t
peelType TNumber = error "peelType: number"
peelType (TAbs _ _ _) = error "peelType: abstraction"

paramTypes :: Type -> [(Maybe Ident, Type)]
paramTypes TNumber = []
paramTypes (TArr _ _) = []
paramTypes (TAbs i t ts) = (i, t):paramTypes ts

namedParamTypes :: Type -> [(Ident, Type)]
namedParamTypes TNumber = []
namedParamTypes (TArr _ _) = []
namedParamTypes (TAbs (Just i) t ts) = (i, t):namedParamTypes ts
namedParamTypes (TAbs Nothing _ _) = error "namedParamTypes: unnamed param (this is a bug)"

data Number = I Int | F Double
  deriving (Show, Data)

data Ident = Ident String
  deriving (Eq, Ord, Data, Show)

data Op = Plus | Minus | Mul | Div
  deriving (Show, Data)

data Expr
  = EConst Number
  | EOp Op Expr Expr -- both args and the result are simple types
  | EArr Type [Expr]

  | EVar Ident

  | EAbs Type {- bindings -} [(Ident, Expr)] Expr
  | EApp Type Expr Expr

  | ESelect Type Expr {- selector -} Expr
  | ERec Type Int Ident Expr -- rec delay |prev| -> expr
  deriving Show

exprType :: Expr -> Type
exprType = undefined

inlineExpr :: Ident -> Expr -> Expr -> Expr
inlineExpr = undefined

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

newtype FuncRef = FuncRef Int deriving (Eq, Ord, Data, Show)

data AllocRegion = ALocal | AGlobal
  deriving (Show, Data)

data SExpr
  = SConst Number
  | SArr Type [Choice]
  | SOp Op Choice Choice

  | SVar Ident
  | SVarNS Ident -- shouldn't be substituted

  | SAbs Type {- bindings -} [(Ident, AllocRegion, Choice)] Choice
  | SApp Type Choice Choice

  | SFuncRef FuncRef
  deriving (Data)

data Choice
  = CChoice Type [Choice] {- selector -} Choice
  | CExpr [(Type, Choice)] SExpr -- selection indices that flow into the inner expression
  | CRec Type Int Ident Choice

  | CFuncRefTable Type [FuncRef] {- selector -} Choice
  deriving (Data)

instance Show SExpr where
  show (SConst n) = show n
  show (SArr t cs) = "[" ++ showType t ++ ": " ++ intercalate ", " (map show cs) ++ "]"
  show (SOp op a b) = "(" ++ show a ++ " " ++ showOp op ++ " " ++ show b ++ ")"
  show (SVar (Ident n)) = n
  show (SVarNS (Ident n)) = n
  show (SAbs t bs body) = 
    "λ" ++ showType t ++ " " ++ showBindings bs ++ " = " ++ show body
    where
      showBindings [] = ""
      showBindings bindings = "{ " ++ intercalate "; " (map showBinding bindings) ++ " }"
      showBinding (Ident n, region, expr) = 
        n ++ "@" ++ showRegion region ++ " = " ++ show expr
      showRegion ALocal = "local"
      showRegion AGlobal = "global"
  show (SApp _ f a) = show f ++ "(" ++ show a ++ ")"
  show (SFuncRef (FuncRef n)) = "funcref#" ++ show n

instance Show Choice where
  show (CChoice t cs idx) = 
    "choice[" ++ showType t ++ "](" ++ intercalate " | " (map show cs) ++ ")[" ++ show idx ++ "]"
  show (CExpr [] expr) = show expr
  show (CExpr idxs expr) = 
    show expr ++ " @ [" ++ intercalate ", " (map showIdxPair idxs) ++ "]"
    where
      showIdxPair (t, idx) = showType t ++ "[" ++ show idx ++ "]"
  show (CFuncRefTable t frs idx) = 
    "table[" ++ showType t ++ "](" ++ intercalate ", " (map showFR frs) ++ ")[" ++ show idx ++ "]"
    where
      showFR (FuncRef n) = "#" ++ show n

instance Show Type where
  show = showType

showType :: Type -> String
showType TNumber = "num"
showType (TArr t dim) = showType t ++ "[" ++ show dim ++ "]"
showType (TAbs Nothing t1 t2) = showType t1 ++ " -> " ++ showType t2
showType (TAbs (Just (Ident n)) t1 t2) = n ++ ":" ++ showType t1 ++ " -> " ++ showType t2

showOp :: Op -> String
showOp Plus = "+"
showOp Minus = "-"
showOp Mul = "*"
showOp Div = "/"

--------------------------------------------------------------------------------

toC :: Monad m => SExpr -> StackM (Type, Expr) m Choice
toC e = do
  idxs <- ST.get
  pure $ CExpr (map (second toChoice) idxs) e

choiceTree :: Monad m => Expr -> StackM (Type, Expr) m Choice
choiceTree (EConst n) = toC (SConst n)
choiceTree (EOp op a b) = toC (SOp op (toChoice a) (toChoice b))
choiceTree (EVar n) = toC (SVar n)
choiceTree (EApp t a b) = toC (SApp t (toChoice a) (toChoice b))
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
choiceTree (ERec t n d e) = CRec t n d <$> choiceTree e

elimConstIndices :: Choice -> Choice
elimConstIndices = transform go
  where
    go :: Choice -> Choice
    -- Eliminate constant index selections by directly selecting the choice
    go (CChoice _ chs (CExpr _ (SConst (I idx)))) = chs !! idx

    -- Keep everything else as-is
    go ch = ch

toChoice :: Expr -> Choice
toChoice = optimize . flip ST.evalState [] . choiceTree
  where
    -- TODO: optimization pipeline
    optimize = elimConstIndices

--------------------------------------------------------------------------------

newtype Unique a = Unique (ST.State Int a)
  deriving (Functor, Applicative, Monad)

runUnique :: Unique a -> a
runUnique (Unique m) = ST.evalState m 0

fresh :: Unique Ident
fresh = Unique $ do
  n <- ST.get
  ST.put (n + 1)
  pure $ Ident ("_captured_" ++ show n)

--------------------------------------------------------------------------------

data Abs = Abs Type {- bindings -} [(Ident, AllocRegion, Choice)] Choice
  deriving Data

instance Show Abs where
  show (Abs t bs e) = show (SAbs t bs e)

data AbsEnv = AbsEnv
  { funcRefMap :: Map FuncRef Abs
  , nextFuncRef :: Int
  } deriving Show

gatherAbstractions :: (Type -> Bool) -> Choice -> (Choice, AbsEnv)
gatherAbstractions allocTablePred choice = flip ST.runState (AbsEnv mempty 0) $ do
  -- Transform all CChoice to CFuncRefTable where predicate holds
  choice' <- transformBiM processCChoice choice

  -- Transform all SAbs to SFuncRef
  transformBiM processSAbs choice'

  where
    processSAbs :: SExpr -> ST.State AbsEnv SExpr
    processSAbs (SAbs t bs body) = do
      fr <- FuncRef <$> ST.gets (.nextFuncRef)

      ST.modify $ \st -> st
        { nextFuncRef = st.nextFuncRef + 1
        , funcRefMap = M.insert fr (Abs t bs body) st.funcRefMap
        }

      pure $ SFuncRef fr
    processSAbs e = pure e

    processCChoice :: Choice -> ST.State AbsEnv Choice
    processCChoice ch@(CChoice t chs idx)
      | allocTablePred t = do
          frIdx <- ST.gets (.nextFuncRef)

          let cht = peelType t
          let frs = [ (FuncRef (frIdx + i), (Abs cht [] ch)) | (i, ch) <- zip [0..] chs ]

          ST.modify $ \st -> st
            { nextFuncRef = st.nextFuncRef + length chs
            , funcRefMap = M.fromList frs <> st.funcRefMap
            }

          pure $ CFuncRefTable t (map fst frs) idx
      | otherwise = pure ch
    processCChoice ch = pure ch

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
          [ [ S.fromList [ n | SVar n <- universeBi body ] ]
          , [ S.fromList [ n | (_, _, b) <- bindings, SVar n <- universeBi b ] ]

          -- Gather transient free vars (by lazily referencing freeVarMap; this works because no mutual recursion between bindings is allowed)
          , [ fvs | SFuncRef fr <- universeBi body, Just fvs <- [ M.lookup fr freeVarMap ] ]
          , [ fvs | (_, _, b) <- bindings, SFuncRef fr <- universeBi b, Just fvs <- [ M.lookup fr freeVarMap ] ]

          , [ fvs | CFuncRefTable _ frs _ <- universeBi body, fr <- frs, Just fvs <- [ M.lookup fr freeVarMap ] ]
          , [ fvs | (_, _, b) <- bindings, CFuncRefTable _ frs _ <- universeBi b, fr <- frs, Just fvs <- [ M.lookup fr freeVarMap ] ]
          ]

markCapturedBindings :: Map FuncRef (Set Ident) -> Map FuncRef Abs -> (Map FuncRef Abs, Map Ident Ident)
markCapturedBindings freeVarMap funcRefMap
  = ( fmap (transformBi (substituteVars substMap)) funcRefMapWithGlobalBindings
    , substMap
    )

  where
    (funcRefMapWithGlobalBindings, substMap) = runUnique $ W.runWriterT (traverse go funcRefMap)

    go :: Abs -> W.WriterT (Map Ident Ident) Unique Abs
    go abs@(Abs t bindings body) = do
      capturedParams <- sequence
        [ (n,) <$> lift fresh
        | (n, _) <- namedParamTypes t
        , S.member n fvs
        ]
      
      W.tell (M.fromList capturedParams)

      pure $ Abs t (bindings' capturedParams) body
      where
        fvs = freeVars abs

        bindings' capturedParams = mconcat
          [ [ if S.member n fvs then (n, AGlobal, body) else b
            | b@(n, _, body) <- bindings
            ]
          , [ (n, AGlobal, CExpr [] (SVarNS o)) | (o, n) <- capturedParams ] 
          ]

    freeVars :: Abs -> Set Ident
    freeVars abs = mconcat $ fmap mconcat
      [ [ fvs
        | SFuncRef fr <- universeBi abs
        , Just fvs <- [ M.lookup fr freeVarMap ]
        ]
      , [ fvs
        | CFuncRefTable _ frs _ <- universeBi abs
        , fr <- frs
        , Just fvs <- [ M.lookup fr freeVarMap ]
        ]
      ]

    -- Substitute variable references using uniplate
    substituteVars :: Map Ident Ident -> Choice -> Choice
    substituteVars subst = transformBi substVar
      where
        substVar (SVar n) = SVar (M.findWithDefault n n subst)
        substVar e = e

-- NEXT
-- * mark captured bindings for storing in global
-- * introduce global bindings for captured arguments, assign argument to them, replace reference to argument with ref to binding in closure
-- * alloc funcref tables for choices
-- * codegen while maintaining focus/select lens
-- * alloc when calling
-- * delay lines (they must have configurable delay); must also be initialized with 0
-- * when choice, call funcref table index or do if/elses
-- ** impure abstractions (e.g. the ones directly or transitively containing a Rec node) must always be computed
-- ** compute the pureness per CChoice entry; at codegen compute the impure ones that were not selected

{-

data CallM a = CallM a

data Value

-- if not in a return context, allocs one
func :: Type -> ([Ref] -> Value) -> CallM FuncRef
func = undefined

-- array ctx -------------------------------------------------------------------

newtype AllocM a = AllocM (ST.State () a)
  deriving (Functor, Applicative, Monad)

newtype FuncRef = FuncRef Int deriving Show
newtype LocalRef = LocalRef Int deriving Show
newtype ArrayRef = ArrayRef Int deriving Show
data Slice = Slice Int Int deriving Show

newSlice :: Type -> Slice
newSlice = undefined

focusSlice :: Int -> Slice -> Slice
focusSlice = undefined

data Ref = RLocal LocalRef | RFuncRef FuncRef | RArr Slice ArrayRef
  deriving Show

-- TODO: optimization is performed on the Choice datatype

-- TODO: alignment in AllocM!

-- TODO: what happens if part of the return value is a capture?
-- this is basically return value ref propagation up the binding chain
-- the most recent returned binding (or argument) gets tagged with "write to return value ref"

allocFuncRef :: AllocM FuncRef
allocFuncRef = undefined

allocArray :: Type -> AllocM ArrayRef
allocArray = undefined

allocLocal :: AllocM LocalRef
allocLocal = undefined

-- slice must be focused on a simple element here
writeElement :: ArrayRef -> Slice -> Number -> AllocM ()
writeElement = undefined

copySlice :: ArrayRef -> LocalRef -> ArrayRef -> Slice -> AllocM ()
copySlice = undefined

writeLocal :: LocalRef -> Number -> AllocM ()
writeLocal = undefined

call :: FuncRef -> [Ref] -> Ref -> AllocM ()
call = undefined

callOp :: Op -> LocalRef -> LocalRef -> LocalRef -> AllocM ()
callOp = undefined

--------------------------------------------------------------------------------

data Env = Env
  { refs :: M.Map Ident (Type, Ref)
  }

newtype Arg = Arg Int deriving Show

data AState = AState
  { funcRefs :: M.Map FuncRef (Type, [Arg], AllocM ())
  , argIdx :: Int
  }

newtype CtxM m a = CtxM (ST.StateT AState (R.ReaderT Env m) a)
  deriving (Functor, Applicative, Monad)

instance MonadTrans CtxM where
  lift f = CtxM $ lift $ lift f

withEnv :: (Env -> Env) -> CtxM m a -> CtxM m a
withEnv f (CtxM m) = CtxM $ ST.StateT $ \st -> R.local f (ST.runStateT m st)

allocRef :: Type -> AllocM Ref
allocRef TNumber = RLocal <$> allocLocal
allocRef t@(TArr _ _) = RArr (newSlice t) <$> allocArray t
allocRef (TAbs _ _) = RFuncRef <$> allocFuncRef

computeIndex :: LocalRef -> [(Type, Index Expr)] -> AllocM ()
computeIndex = undefined

-- type is needed for type signature in WASM/C
funcRef :: FuncRef -> Type -> ([Ref] -> Ref -> CtxM AllocM ()) -> CtxM AllocM ()
funcRef fr t f = CtxM $ do
  st <- ST.get
  sequence_
    [ undefined
    | paramType <- paramTypes t
    ]
  undefined

allocExpr :: [(Type, Index Expr)] -> Ref -> SExpr Expr -> CtxM AllocM ()
allocExpr [] (RLocal ref) (SConst n) = lift $ writeLocal ref n
allocExpr [] (RArr slice ref) (SConst n) = lift $ writeElement ref slice n
allocExpr [] (RArr slice ref) (SArr _ es) = sequence_
  [ allocChoice (RArr (focusSlice i slice) ref) (toChoice e)
  | (i, e) <- zip [0..] es
  ]
allocExpr [] (RLocal ref) (SOp op a b) = do
  aref <- lift $ allocLocal
  bref <- lift $ allocLocal
  allocChoice (RLocal aref) (toChoice a)
  allocChoice (RLocal bref) (toChoice b)
  lift $ callOp op aref bref ref
allocExpr idxs ref (SExtern _ _ _) = undefined
allocExpr [] (RFuncRef fref) (SAbs (Abs t paramNames bindings expr)) = do
  bindingRefs' <- lift $ sequence
    [ do
        ref <- allocRef (exprType bexpr)
        pure (bname, (t, ref))
    | (bname, bexpr) <- bindings
    ]

  let bindingRefs = M.fromList bindingRefs'

  let innerEnv argRefs env = env 
        { refs = mconcat
            [ bindingRefs
            , M.fromList
                [ (paramName, (paramType, argRef))
                | (argRef, (paramName, paramType)) <- zip argRefs (zip paramNames (paramTypes t))
                ]
            , env.refs
            ]
        }

  sequence_
    [ funcRef fr t $ \args ref -> withEnv (innerEnv args) (allocChoice ref (toChoice bexpr))
    | ((_, bexpr), (_, (t, RFuncRef fr))) <- zip bindings bindingRefs'
    ]

  funcRef fref t $ \args ref -> withEnv (innerEnv args) (allocChoice ref (toChoice expr))
allocExpr idxs ref (SApp _ n args) = do
  env <- R.ask
   
   -- TODO if no args just use ref

  case M.lookup n env.refs of
    Just (t, RFuncRef fr) -> do
      argRefs <- sequence
        [ do
            ref <- lift $ allocRef argType
            allocChoice ref (toChoice arg)
            pure ref
        | (arg, argType) <- zip args (paramTypes t)
        ]

      case drop (length args) (paramTypes t) of
        -- full application
        [] -> case idxs of
          -- no spillover indices
          [] -> lift $ call fr argRefs ref
          idxs' -> do
            let tempType = peelType t (length idxs')

            lift $ do
              tempRef <- allocArray tempType
              call fr argRefs (RArr (newSlice tempType) tempRef)
              lidx <- allocLocal
              computeIndex lidx idxs'

              case ref of
                RArr slice toRef -> copySlice tempRef lidx toRef slice
                e -> error $ "allocExpr: SApp: RArr: " <> show e <> " (this is a bug)"

        params' -> lift $ do
          when (not $ null idxs) $
            error $ "allocExpr: SApp: curried function with spillover indices: (this is a bug)"

          case ref of
            RFuncRef curriedFr -> 
              funcRef curriedFr (TAbs params' (returnType t)) $ \ref' -> do
                curriedArgRefs <- sequence [ arg i | (i, _) <- zip [0..] params' ]
                call fr (argRefs <> curriedArgRefs) ref'

            ref' ->  error $ "allocExpr: SApp: ref: " <> show ref' <> " (this is a bug)"
    e -> error $ "allocExpr: SApp: " <> show e <> " (this is a bug)"
allocExpr _ _ _ = error "allocExpr"

allocChoice :: Ref -> Choice Expr -> CtxM AllocM ()
allocChoice ref (CExpr idxs e) = allocExpr idxs ref e

--------------------------------------------------------------------------------

t :: [Int] -> Type
t [] = TNumber
t (dim:dims) = TArr (t dims) dim

e1 :: Expr
e1 = ESelect (t [3, 2]) (
  ESelect (t [2]) (
      EArr (t [3])
        [ (EArr (t [2]) [EConst $ I 0, EConst $ I 1])
        , (EArr (t [2]) [EConst $ I 2, EConst $ I 3])
        , (EArr (t [2]) [EConst $ I 4, EConst $ I 5])
        ])
    (IdxConst 2))
  (IdxConst 1)


e2 :: Expr
e2 = ESelect (t [3, 2]) (
  ESelect (t [2]) (
      EArr (t [3])
        [ (EArr (t [2]) [EConst $ I 0, EConst $ I 1])
        , (EExtern (t [2]) (Ident "global") [])
        , (EArr (t [2]) [EConst $ I 4, EConst $ I 5])
        ])
    (IdxConst 1))
  (IdxConst 1)

-}

--------------------------------------------------------------------------------
-- Test expressions for markCapturedBindings

-- Test 1: Simple abstraction with no captures
testChoice1 :: Choice
testChoice1 = CExpr [] $ SAbs
  (TAbs (Just (Ident "x")) TNumber TNumber)
  [(Ident "x", ALocal, CExpr [] (SConst (I 0)))]
  (CExpr [] (SVar (Ident "x")))

-- Test 2: Abstraction that captures a parameter in a nested abstraction
testChoice2 :: Choice
testChoice2 = CExpr [] $ SAbs
  (TAbs (Just (Ident "x")) TNumber (TAbs (Just (Ident "y")) TNumber TNumber))
  [(Ident "z", ALocal, CExpr [] (SConst (I 0)))]
  (CExpr [] $ SAbs
    (TAbs (Just (Ident "a")) TNumber TNumber)
    [(Ident "b", ALocal, CExpr [] (SConst (I 1)))]
    (CExpr [] $ SOp Plus (CExpr [] (SVar (Ident "x"))) (CExpr [] (SVar (Ident "z")))))

-- Test 3: Abstraction with a binding that references a parameter
testChoice3 :: Choice
testChoice3 = CExpr [] $ SAbs
  (TAbs (Just (Ident "x")) TNumber TNumber)
  [ (Ident "x", ALocal, CExpr [] (SConst (I 5)))
  , (Ident "y", ALocal, CExpr [] (SVar (Ident "x")))
  ]
  (CExpr [] (SVar (Ident "y")))

-- Test 4: Nested abstractions with multiple captures
testChoice4 :: Choice
testChoice4 = CExpr [] $ SAbs
  (TAbs (Just (Ident "a")) TNumber (TAbs (Just (Ident "b")) TNumber TNumber))
  [(Ident "bnd_a", ALocal, CExpr [] (SConst (I 1)))]
  (CExpr [] $ SAbs
    (TAbs (Just (Ident "c")) TNumber TNumber)
    [ (Ident "bnd_b", ALocal, CExpr [] (SVar (Ident "bnd_a")))
    , (Ident "bnd_c", ALocal, CExpr [] (SVar (Ident "a")))
    ]
    (CExpr [] $ SOp Mul (CExpr [] (SVar (Ident "c"))) (CExpr [] (SVar (Ident "b")))))

-- Test 4: Nested abstractions with multiple captures
testChoice4_2 :: Choice
testChoice4_2 = CExpr [] $ SAbs
  (TAbs (Just (Ident "a")) TNumber (TAbs (Just (Ident "b")) TNumber (TAbs (Just (Ident "z")) TNumber TNumber)))
  [(Ident "bnd_a", ALocal, CExpr [] (SConst (I 1)))]
  (CExpr [] $ SAbs
    (TAbs (Just (Ident "c")) TNumber TNumber)
    [ (Ident "bnd_b", ALocal, CExpr [] (SVar (Ident "a")))
    , (Ident "bnd_c", ALocal, CExpr [] (SVar (Ident "z")))
    ]
    (CChoice TNumber
      [ (CExpr [] $ SOp Mul (CExpr [] (SVar (Ident "c"))) (CExpr [] (SVar (Ident "b"))))
      , (CExpr [] $ SOp Mul (CExpr [] (SVar (Ident "c"))) (CExpr [] (SVar (Ident "z"))))
      ] (CExpr [] $ SOp Mul (CExpr [] (SVar (Ident "bnd_a"))) (CExpr [] (SVar (Ident "z"))))))

testChoice4_3 :: Choice
testChoice4_3 = CExpr [] $ SAbs
  (TAbs (Just (Ident "a")) TNumber (TAbs (Just (Ident "b")) TNumber (TAbs (Just (Ident "z")) TNumber TNumber)))
  [(Ident "bnd_a", ALocal, CExpr [] (SConst (I 1)))]
  (CExpr [] $ SAbs
    (TAbs (Just (Ident "c")) TNumber TNumber)
    [ (Ident "bnd_b", ALocal, CExpr [] (SVar (Ident "a")))
    , (Ident "bnd_c", ALocal, CExpr [] (SVar (Ident "z")))
    ]
    (CChoice (TArr TNumber 3)
      [ (CExpr [] $ SOp Mul (CExpr [] (SVar (Ident "c"))) (CExpr [] (SVar (Ident "b"))))
      , (CExpr [] $ SOp Mul (CExpr [] (SVar (Ident "c"))) (CExpr [] (SVar (Ident "z"))))
      , (CChoice (TArr TNumber 3)
          [ (CExpr [] $ SOp Mul (CExpr [] (SVar (Ident "c"))) (CExpr [] (SVar (Ident "b"))))
          , (CExpr [] $ SOp Mul (CExpr [] (SVar (Ident "c"))) (CExpr [] (SVar (Ident "z"))))
          ] (CChoice (TArr TNumber 3)
                 [ (CExpr [] $ SConst $ I 1)
                 , (CExpr [] $ SOp Mul (CExpr [] (SVar (Ident "c"))) (CExpr [] (SVar (Ident "z"))))
                 ] (CExpr [] $ SConst $ I 0))) 
      ] (CExpr [] $ SConst $ I 2)))

-- Test 5: Abstraction with free variable (not captured, just free)
testChoice5 :: Choice
testChoice5 = CExpr [] $ SAbs
  (TAbs (Just (Ident "x")) TNumber TNumber)
  [(Ident "x", ALocal, CExpr [] (SConst (I 0)))]
  (CExpr [] $ SOp Plus (CExpr [] (SVar (Ident "x"))) (CExpr [] (SVar (Ident "freeVar"))))

-- Test 6: Complex case with binding that captures and is itself captured
testChoice6 :: Choice
testChoice6 = CExpr [] $ SAbs
  (TAbs (Just (Ident "x")) TNumber (TAbs (Just (Ident "y")) TNumber TNumber))
  [ (Ident "x", ALocal, CExpr [] (SConst (I 10)))
  , (Ident "helper", ALocal, CExpr [] $ SAbs
      (TAbs (Just (Ident "z")) TNumber TNumber)
      [(Ident "z", ALocal, CExpr [] (SConst (I 0)))]
      (CExpr [] $ SOp Plus (CExpr [] (SVar (Ident "x"))) (CExpr [] (SVar (Ident "z")))))
  ]
  (CExpr [] $ SAbs
    (TAbs (Just (Ident "y")) TNumber TNumber)
    [(Ident "y", ALocal, CExpr [] (SConst (I 20)))]
    (CExpr [] $ SApp TNumber (CExpr [] (SVar (Ident "helper"))) (CExpr [] (SVar (Ident "y")))))

testMark :: Choice -> (Map FuncRef Abs, Map Ident Ident)
testMark ch = markCapturedBindings freeVarMap env.funcRefMap
  where
    (ch', env) = gatherAbstractions (const True) ch
    freeVarMap = gatherFreeVars env.funcRefMap
