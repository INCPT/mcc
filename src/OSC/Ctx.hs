{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}

module OSC.Ctx where

import Data.Bifunctor (second)
import Data.Data (Typeable, Data)
import Data.Functor.Identity
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
  deriving (Data, Show)

sizeOfType :: Type -> Int
sizeOfType TNumber = 4
sizeOfType (TArr t dim) = sizeOfType t * dim
sizeOfType (TAbs _ _ _) = 4 -- funcref is an integer

returnType :: Type -> Type
returnType TNumber = TNumber
returnType t@(TArr _ _) = t
returnType (TAbs _ _ t) = t

peelType :: Type -> Type
peelType = undefined

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

data Index a = IdxConst Int | IdxVar a
  deriving (Show, Functor, Foldable, Traversable, Data)

data Op = Plus | Minus | Mul | Div
  deriving (Show, Data)

data Expr
  = EConst Number
  | EOp Op Expr Expr -- both args and the result are simple types
  | EArr Type [Expr]

  | EVar Ident

  | EAbs Type {- bindings -} [(Ident, Expr)] Expr
  | EApp Type Expr Expr

  | ESelect Type Expr (Index Expr)
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

  | SAbs Type {- bindings -} [(Ident, AllocRegion, Choice)] Choice
  | SApp Type Choice Choice

  | SFuncRef FuncRef
  deriving (Show, Data)

data Choice
  = CChoice Type [Choice] (Index Choice)
  | CExpr [(Type, Index (Choice))] SExpr -- selection indices that flow into the inner expression

  | CFuncRefTable Type [FuncRef] (Index Choice)
  deriving (Show, Data)

traverseChoice
  :: Monad f
  => (Choice -> f Choice)
  -> (SExpr -> f SExpr)
  -> Choice
  -> f Choice
traverseChoice fChoice fSExpr = go
  where
    go (CChoice t choices idx) = do
      choices' <- traverse go choices
      idx' <- sequenceA $ fmap go idx
      fChoice (CChoice t choices' idx')

    go (CExpr idxs sexpr) = do
      idxs' <- traverse (\(t, idx) -> (t,) <$> traverse go idx) idxs
      sexpr' <- goSExpr sexpr
      sexpr'' <- fSExpr sexpr'
      fChoice (CExpr idxs' sexpr'')

    go (CFuncRefTable t frs idx) = do
      idx' <- sequenceA $ fmap go idx
      fChoice (CFuncRefTable t frs idx')

    goSExpr (SConst n) = pure (SConst n)
    goSExpr (SArr t cs) = SArr t <$> traverse go cs
    goSExpr (SOp op a b) = SOp op <$> go a <*> go b
    goSExpr (SVar n) = pure (SVar n)
    goSExpr (SAbs t bs c) = SAbs t <$> traverse (sequenceA2 . fmap go) bs <*> go c
      where
        sequenceA2 (a, b, f) = (,,) <$> pure a <*> pure b <*> f
    goSExpr (SApp t f a) = SApp t <$> go f <*> go a
    goSExpr (SFuncRef fr) = pure (SFuncRef fr)

--------------------------------------------------------------------------------

toC :: Monad m => SExpr -> StackM (Type, Index Expr) m Choice
toC e = do
  idxs <- ST.get
  pure $ CExpr (map (second (fmap toChoice)) idxs) e

choiceTree :: Monad m => Expr -> StackM (Type, Index Expr) m Choice
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
      pure $ CChoice t es' (fmap toChoice idx)
    Nothing -> pure $ CExpr [] (SArr t $ map toChoice es)
choiceTree (ESelect t e idx) = do
  push (t, idx)
  c <- choiceTree e
  _ <- pop
  pure c
choiceTree (ERec _ _ _ e) = choiceTree e -- TODO: need to inline ident with delay boxes

elimIndices :: [(Type, Index Choice)] -> [(Type, Index Choice)]
elimIndices = map (\(t, idx) -> (t, fmap elimConstIndices idx))

-- TODO: optimization, cluster generation and so on go here
elimConstIndices :: Choice -> Choice
elimConstIndices (CExpr idxs (SConst n)) = CExpr (elimIndices idxs) (SConst n)
elimConstIndices (CExpr idxs (SVar n)) = CExpr (elimIndices idxs) (SVar n)
elimConstIndices (CExpr idxs (SApp t a b)) = CExpr (elimIndices idxs) (SApp t (elimConstIndices a) (elimConstIndices b))
elimConstIndices (CExpr idxs (SArr t es)) = CExpr (elimIndices idxs) (SArr t $ map elimConstIndices es)
elimConstIndices (CChoice _ chs (IdxConst idx)) = elimConstIndices (chs !! idx)
elimConstIndices (CChoice t chs idx) = CChoice t (map elimConstIndices chs) idx

elimConstIndices _ = undefined

--------------------------------------------------------------------------------

elimIndicesU :: [(Type, Index Choice)] -> [(Type, Index Choice)]
elimIndicesU = map (\(t, idx) -> (t, fmap elimConstIndicesU idx))

-- Uniplate version
elimConstIndicesU :: Choice -> Choice
elimConstIndicesU = transform go
  where
    go :: Choice -> Choice
    -- Eliminate constant index selections by directly selecting the choice
    go (CChoice _ chs (IdxConst idx)) = chs !! idx

    -- Recursively eliminate indices in CExpr
    go (CExpr idxs sexpr) = CExpr (elimIndicesU idxs) sexpr

    -- Keep everything else as-is
    go ch = ch

toChoice :: Expr -> Choice
toChoice = elimConstIndices . flip ST.evalState [] . choiceTree

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

data MarkEnv = MarkEnv
  { freeVars :: Set Ident
  , capturedParamMap :: Map Ident Ident
  }

instance Semigroup MarkEnv where
  MarkEnv a b <> MarkEnv c d = MarkEnv (a <> c) (b <> d)

instance Monoid MarkEnv where
  mempty = MarkEnv mempty mempty

markCapturedBindings :: Choice -> Choice
markCapturedBindings choice = substituteVars env.capturedParamMap choice'
  where
    (choice', env) = runUnique (W.runWriterT (descendBiM processSAbs choice))

    -- Substitute variable references using uniplate
    substituteVars :: Map Ident Ident -> Choice -> Choice
    substituteVars subst = transformBi substVar
      where
        substVar (SVar n) = SVar (M.findWithDefault n n subst)
        substVar e = e

    -- Collect free variables from SExpr
    collectSExprFreeVars :: SExpr -> Set Ident
    collectSExprFreeVars (SVar n) = S.singleton n
    collectSExprFreeVars _ = S.empty

    processSAbs :: SExpr -> W.WriterT MarkEnv Unique SExpr
    processSAbs e@(SVar n) = do
      -- Report this variable as free
      W.tell $ mempty { freeVars = S.singleton n }
      pure e
    
    processSAbs (SAbs t bindings body) = do
      -- Extract parameter names and types from the function type
      let paramMap = M.fromList (namedParamTypes t)
      
      -- Collect all bindings (name, region)
      let bindingMap = M.fromList [(n, r) | (n, r, _) <- bindings]
      
      -- Process binding expressions and collect their free variables
      (processedBs, bsEnv) <- lift $ W.runWriterT $ sequence
        [ do
            expr' <- descendBiM processSAbs expr
            pure (n, r, expr')
        | (n, r, expr) <- bindings
        ]
      
      -- Process body and collect its free variables
      (body', bodyEnv) <- lift $ W.runWriterT $ descendBiM processSAbs body
      
      -- All bound names (parameters and bindings)
      let bound = S.fromList [n | (n, _, _) <- bindings] <> M.keysSet paramMap
      
      -- Captured = free in body AND bound in outer scope
      let capturedParams = M.filterWithKey (\n _ -> S.member n bodyEnv.freeVars && M.member n paramMap) paramMap
      let capturedBindings = M.filterWithKey (\n _ -> S.member n bsEnv.freeVars && M.member n bindingMap) bindingMap
      
      -- Create new bindings for captured parameters
      capturedParams <- sequence
        [ do
            newName <- lift fresh
            pure (paramName, newName)
        | paramName <- M.keys capturedParams
        ]
      
      W.tell $ mempty
        -- Filter out bound variables - only report truly free variables up
        { freeVars = (bodyEnv.freeVars <> bsEnv.freeVars) \\ bound
        , capturedParamMap = M.fromList capturedParams
        }
      
      -- Update bindings: mark captured bindings as AGlobal and add new bindings for captured params
      let updatedBindings = mconcat
            [ [ case M.lookup n capturedBindings of
                  Just _ -> (n, AGlobal, expr')  -- Mark as global if captured
                  Nothing -> (n, r, expr')       -- Keep original region
              | (n, r, expr') <- processedBs
              ]
            , [ (newName, AGlobal, CExpr [] (SVar paramName))  -- New binding for captured param
              | (paramName, newName) <- capturedParams
              ]
            ]
      
      pure (SAbs t updatedBindings body')
    
    processSAbs e = do
      -- Report any free variables in this expression
      W.tell $ mempty { freeVars = collectSExprFreeVars e }
      pure e

--------------------------------------------------------------------------------

data AbsEnv = AbsEnv
  { funcRefMap :: Map FuncRef (Type, [(Ident, AllocRegion, Choice)], Choice)
  , nextFuncRef :: Int
  }

gatherAbstractions :: (Type -> Bool) -> Choice -> (Choice, AbsEnv)
gatherAbstractions allocTablePred choice = flip ST.runState (AbsEnv mempty 0) $ do
  -- First pass: transform all SAbs to SFuncRef
  choice' <- transformBiM processSAbs choice

  -- Second pass: transform all CChoice to CFuncRefTable where predicate holds
  transformBiM processCChoice choice'

  where
    processSAbs :: SExpr -> ST.State AbsEnv SExpr
    processSAbs (SAbs t bs body) = do
      fr <- FuncRef <$> ST.gets (.nextFuncRef)

      ST.modify $ \st -> st
        { nextFuncRef = st.nextFuncRef + 1
        , funcRefMap = M.insert fr (t, bs, body) st.funcRefMap
        }

      pure $ SFuncRef fr
    processSAbs e = pure e

    processCChoice :: Choice -> ST.State AbsEnv Choice
    processCChoice ch@(CChoice t chs idx)
      | allocTablePred t = do
          frIdx <- ST.gets (.nextFuncRef)

          let cht = peelType t
          let frs = [ (FuncRef (frIdx + i), (cht, [], ch)) | (i, ch) <- zip [0..] chs ]

          ST.modify $ \st -> st
            { nextFuncRef = st.nextFuncRef + length chs
            , funcRefMap = M.fromList frs <> st.funcRefMap
            }

          pure $ CFuncRefTable t (map fst frs) idx
      | otherwise = pure ch
    processCChoice ch = pure ch

-- NEXT
-- * mark captured bindings for storing in global
-- * introduce global bindings for captured arguments, assign argument to them, replace reference to argument with ref to binding in closure
-- * alloc funcref tables for choices
-- * codegen while maintaining focus/select lens
-- * alloc when calling
-- * when choice, call funcref table index or do if/elses

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
