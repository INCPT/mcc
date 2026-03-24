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
  deriving (Data)

data Choice
  = CChoice Type [Choice] (Index Choice)
  | CExpr [(Type, Index Choice)] SExpr -- selection indices that flow into the inner expression

  | CFuncRefTable Type [FuncRef] (Index Choice)
  deriving (Data)

instance Show SExpr where
  show (SConst n) = show n
  show (SArr t cs) = "[" ++ showType t ++ ": " ++ intercalate ", " (map show cs) ++ "]"
  show (SOp op a b) = "(" ++ show a ++ " " ++ showOp op ++ " " ++ show b ++ ")"
  show (SVar (Ident n)) = n
  show (SAbs t bs body) = 
    "λ" ++ showType t ++ " " ++ showBindings bs ++ " = " ++ show body
    where
      showBindings [] = ""
      showBindings bindings = "{ " ++ intercalate "; " (map showBinding bindings) ++ " }"
      showBinding (Ident n, region, expr) = 
        n ++ "@" ++ showRegion region ++ " = " ++ show expr
      showRegion ALocal = "local"
      showRegion AGlobal = "global"
  show (SApp t f a) = show f ++ "(" ++ show a ++ ")"
  show (SFuncRef (FuncRef n)) = "funcref#" ++ show n

instance Show Choice where
  show (CChoice t cs idx) = 
    "choice[" ++ showType t ++ "](" ++ intercalate " | " (map show cs) ++ ")[" ++ showIndex idx ++ "]"
  show (CExpr [] expr) = show expr
  show (CExpr idxs expr) = 
    show expr ++ " @ [" ++ intercalate ", " (map showIdxPair idxs) ++ "]"
    where
      showIdxPair (t, idx) = showType t ++ "[" ++ showIndex idx ++ "]"
  show (CFuncRefTable t frs idx) = 
    "table[" ++ showType t ++ "](" ++ intercalate ", " (map showFR frs) ++ ")[" ++ showIndex idx ++ "]"
    where
      showFR (FuncRef n) = "#" ++ show n

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

showIndex :: Index Choice -> String
showIndex (IdxConst n) = show n
showIndex (IdxVar c) = show c

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
  } deriving Show

instance Semigroup MarkEnv where
  MarkEnv a b <> MarkEnv c d = MarkEnv (a <> c) (b <> d)

instance Monoid MarkEnv where
  mempty = MarkEnv mempty mempty

markCapturedBindings :: Choice -> (Choice, MarkEnv)
markCapturedBindings choice = (substituteVars env.capturedParamMap choice', env)
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

markCapturedBindings2 :: Choice -> (Choice, MarkEnv)
markCapturedBindings2 choice = (substituteVars env.capturedParamMap choice', env)
  where
    (choice', env) = runUnique (W.runWriterT $ go choice)

    -- Substitute variable references using uniplate
    substituteVars :: Map Ident Ident -> Choice -> Choice
    substituteVars subst = transformBi substVar
      where
        substVar (SVar n) = SVar (M.findWithDefault n n subst)
        substVar e = e
    
    indexes :: [(Type, Index Choice)] -> W.WriterT MarkEnv Unique [(Type, Index Choice)]
    indexes idxs = sequence
      [ (t,) <$> sequenceA (fmap go idx)
      | (t, idx) <- idxs
      ]
    
    cexpr :: Choice -> (SExpr -> W.WriterT MarkEnv Unique SExpr) -> W.WriterT MarkEnv Unique Choice
    cexpr (CExpr idxs sexpr) f = CExpr <$> indexes idxs <*> f sexpr
    cexpr (CChoice t chs idx) _ = CChoice <$> pure t <*> traverse go chs <*> sequenceA (fmap go idx)
    cexpr (CFuncRefTable t fs idx) _ = CFuncRefTable <$> pure t <*> pure fs <*> sequenceA (fmap go idx)

    go :: Choice -> W.WriterT MarkEnv Unique Choice
    go (CExpr idxs (SAbs t bindings body)) = do
      -- Extract parameter names and types from the function type
      let paramMap = M.fromList (namedParamTypes t)
      
      -- Collect all bindings (name, region)
      let bindingMap = M.fromList [(n, r) | (n, r, _) <- bindings]
      
      -- Process binding expressions and collect their free variables
      (processedBs, bsEnv) <- lift $ W.runWriterT $ sequence
        [ do
            expr' <- go expr
            pure (n, r, expr')
        | (n, r, expr) <- bindings
        ]
      
      -- Process body and collect its free variables
      (body', bodyEnv) <- lift $ W.runWriterT $ go body
      
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
      
      pure (CExpr idxs (SAbs t updatedBindings body'))

    go e = cexpr e $ \case
      e@(SConst _) -> pure e

      SArr t as -> do
        as' <- traverse go as
        pure $ SArr t as'

      SOp op a b -> do
        a' <- go a
        b' <- go b
        pure $ SOp op a' b'

      e@(SVar n) -> do
        W.tell $ mempty { freeVars = S.singleton n }
        pure e
    
      SApp t a b -> do
        a' <- go a
        b' <- go b
        pure $ SApp t a' b'

      SAbs _ _ _ -> error "SAbs: should be pattern matched in go (this is a bug)"

      e@(SFuncRef _) -> pure e

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
  [(Ident "a", ALocal, CExpr [] (SConst (I 1)))]
  (CExpr [] $ SAbs
    (TAbs (Just (Ident "b")) TNumber TNumber)
    [ (Ident "b", ALocal, CExpr [] (SConst (I 2)))
    , (Ident "c", ALocal, CExpr [] (SVar (Ident "a")))
    ]
    (CExpr [] $ SOp Mul (CExpr [] (SVar (Ident "c"))) (CExpr [] (SVar (Ident "b")))))

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

-- Helper function to run the test
runMarkTest :: Choice -> (Choice, MarkEnv)
runMarkTest = markCapturedBindings
