{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}

module OSC.Ctx where

import Data.Bifunctor (second)
import Data.Functor.Identity
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Control.Monad.Trans (MonadTrans, lift)
import qualified Control.Monad.Reader as R
import qualified Control.Monad.State as ST

data Type = TNumber | TArr Type {- length -} Int | TAbs (Maybe Ident) Type Type
  deriving Show

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
  deriving Show

data Ident = Ident String
  deriving (Eq, Ord, Show)

data Index a = IdxConst Int | IdxVar a
  deriving (Show, Functor, Foldable, Traversable)

data Op = Plus | Minus | Mul | Div
  deriving Show

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

newtype FuncRef = FuncRef Int deriving (Eq, Ord, Show)

data AllocRegion = ALocal | AGlobal
  deriving (Show)

data SExpr
  = SConst Number
  | SArr Type [Choice]
  | SOp Op Choice Choice

  | SVar Ident

  | SAbs Type {- bindings -} [(Ident, AllocRegion, Choice)] Choice
  | SApp Type Choice Choice

  | SFuncRef FuncRef
  deriving (Show)

data Choice
  = CChoice Type [Choice] (Index Choice)
  | CExpr [(Type, Index (Choice))] SExpr -- selection indices that flow into the inner expression

  | CFuncRefTable Type [FuncRef] (Index Choice)
  deriving (Show)

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

toChoice :: Expr -> Choice
toChoice = elimConstIndices . flip ST.evalState [] . choiceTree

--------------------------------------------------------------------------------

newtype UniqueM m a = UniqueM (ST.StateT Int m a)
  deriving (Functor, Applicative, Monad, MonadTrans)

uniqueName :: Monad m => UniqueM m Ident
uniqueName = UniqueM $ do
  n <- ST.get
  ST.put (n + 1)
  pure $ Ident ("_captured_" ++ show n)

-- Environment tracking bindings and parameters in scope
data MarkEnv = MarkEnv
  { bindings :: Map Ident AllocRegion  -- Current bindings in scope
  , params :: Map Ident Type           -- Current parameters in scope
  , captured :: Map Ident Ident        -- Mapping from captured params to new bindings
  }

emptyMarkEnv :: MarkEnv
emptyMarkEnv = MarkEnv M.empty M.empty M.empty

-- Track which identifiers are referenced
type ReferencedSet = Set Ident

markCapturedBindings :: Monad m => Choice -> UniqueM m Choice
markCapturedBindings choice = UniqueM $ ST.evalStateT (R.runReaderT (markChoice choice) emptyMarkEnv) 0
  where
    markChoice :: Monad m => Choice -> R.ReaderT MarkEnv (ST.StateT Int m) Choice
    markChoice = traverseChoice pure fSExpr

    fSExpr :: Monad m => SExpr -> R.ReaderT MarkEnv (ST.StateT Int m) SExpr
    fSExpr (SAbs t bs body) = do
      env <- R.ask
      
      -- Extract parameter names and types from the function type
      let paramList = namedParamTypes t
      let paramMap = M.fromList paramList
      
      -- Collect all bindings (name, region, expr)
      let bindingList = [ (n, r) | (n, r, _) <- bs ]
      let bindingMap = M.fromList bindingList
      
      -- Find all references in the body
      let refs = findReferences body
      
      -- Determine which params and bindings are captured (referenced and defined in outer scope)
      let capturedParams = M.filterWithKey (\n _ -> S.member n refs && M.member n env.params) paramMap
      let capturedBindings = M.filterWithKey (\n _ -> S.member n refs && M.member n env.bindings) bindingMap
      
      -- Create new bindings for captured parameters
      newBindings <- sequence
        [ do
            newName <- lift $ do
              n <- ST.get
              ST.put (n + 1)
              pure $ Ident ("_captured_" ++ show n)
            pure (paramName, newName)
        | paramName <- M.keys capturedParams
        ]
      
      let capturedParamMap = M.fromList newBindings
      
      -- Update bindings: mark captured bindings as AGlobal and add new bindings for captured params
      let updatedBindings = 
            [ case M.lookup n capturedBindings of
                Just _ -> (n, AGlobal, expr)  -- Mark as global if captured
                Nothing -> (n, r, expr)       -- Keep original region
            | (n, r, expr) <- bs
            ] ++
            [ (newName, AGlobal, CExpr [] (SVar paramName))  -- New binding for captured param
            | (paramName, newName) <- newBindings
            ]
      
      -- Substitute captured param references with new binding references in body
      let substitutedBody = substituteRefs capturedParamMap body
      
      -- Recursively process the body with updated environment
      let newEnv = env
            { bindings = bindingMap <> env.bindings
            , params = paramMap <> env.params
            , captured = capturedParamMap <> env.captured
            }
      
      processedBody <- R.local (const newEnv) (markChoice substitutedBody)
      processedBindings <- sequence
        [ do
            expr' <- R.local (const newEnv) (markChoice expr)
            pure (n, r, expr')
        | (n, r, expr) <- updatedBindings
        ]
      
      pure $ SAbs t processedBindings processedBody
    
    fSExpr (SVar n) = do
      env <- R.ask
      -- If this variable is a captured param, use the new binding name
      case M.lookup n env.captured of
        Just newName -> pure $ SVar newName
        Nothing -> pure $ SVar n
    
    fSExpr e = pure e
    
    -- Find all variable references in a Choice
    findReferences :: Choice -> ReferencedSet
    findReferences (CChoice _ chs idx) = 
      mconcat (map findReferences chs) <> foldMap findReferences idx
    findReferences (CExpr idxs sexpr) = 
      mconcat [ foldMap findReferences idx | (_, idx) <- idxs ] <> findRefsSExpr sexpr
    findReferences (CFuncRefTable _ _ idx) = 
      foldMap findReferences idx
    
    findRefsSExpr :: SExpr -> ReferencedSet
    findRefsSExpr (SConst _) = S.empty
    findRefsSExpr (SArr _ cs) = mconcat (map findReferences cs)
    findRefsSExpr (SOp _ a b) = findReferences a <> findReferences b
    findRefsSExpr (SVar n) = S.singleton n
    findRefsSExpr (SAbs _ bs body) = 
      mconcat [ findReferences expr | (_, _, expr) <- bs ] <> findReferences body
    findRefsSExpr (SApp _ f a) = findReferences f <> findReferences a
    findRefsSExpr (SFuncRef _) = S.empty
    
    -- Substitute variable references in a Choice
    substituteRefs :: Map Ident Ident -> Choice -> Choice
    substituteRefs subst (CChoice t chs idx) = 
      CChoice t (map (substituteRefs subst) chs) (fmap (substituteRefs subst) idx)
    substituteRefs subst (CExpr idxs sexpr) = 
      CExpr [ (t, fmap (substituteRefs subst) idx) | (t, idx) <- idxs ] (substSExpr subst sexpr)
    substituteRefs subst (CFuncRefTable t frs idx) = 
      CFuncRefTable t frs (fmap (substituteRefs subst) idx)
    
    substSExpr :: Map Ident Ident -> SExpr -> SExpr
    substSExpr _ (SConst n) = SConst n
    substSExpr subst (SArr t cs) = SArr t (map (substituteRefs subst) cs)
    substSExpr subst (SOp op a b) = SOp op (substituteRefs subst a) (substituteRefs subst b)
    substSExpr subst (SVar n) = SVar (M.findWithDefault n n subst)
    substSExpr subst (SAbs t bs body) = 
      SAbs t [ (n, r, substituteRefs subst expr) | (n, r, expr) <- bs ] (substituteRefs subst body)
    substSExpr subst (SApp t f a) = SApp t (substituteRefs subst f) (substituteRefs subst a)
    substSExpr _ (SFuncRef fr) = SFuncRef fr

--------------------------------------------------------------------------------

data AbsEnv = AbsEnv
  { funcRefMap :: Map FuncRef (Type, [(Ident, AllocRegion, Choice)], Choice)
  , nextFuncRef :: Int
  }

gatherAbstractions :: (Type -> Bool) -> Choice -> ST.State AbsEnv Choice
gatherAbstractions allocTablePred = traverseChoice fChoice fSExpr
  where
    fChoice :: Choice -> ST.State AbsEnv Choice
    fChoice ch@(CChoice t chs idx)
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
    fChoice ch = pure ch

    fSExpr :: SExpr -> ST.State AbsEnv SExpr
    fSExpr (SAbs t bs body) = do
      fr <- FuncRef <$> ST.gets (.nextFuncRef)

      ST.modify $ \st -> st
        { nextFuncRef = st.nextFuncRef + 1
        , funcRefMap = M.insert fr (t, bs, body) st.funcRefMap
        }

      pure $ SFuncRef fr
    fSExpr e = pure e

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
