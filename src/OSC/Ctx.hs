{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}

module OSC.Ctx where

import Data.Functor.Identity
import Control.Monad (when)
import Control.Monad.Trans (MonadTrans, lift)
import qualified Control.Monad.Reader as R
import qualified Control.Monad.State as ST
import qualified Data.Map as M

data Type = TNumber | TArr Type {- length -} Int | TAbs [Type] Type
  deriving Show

sizeOfType :: Type -> Int
sizeOfType TNumber = 4
sizeOfType (TArr t dim) = sizeOfType t * dim
sizeOfType (TAbs _ _) = 4 -- funcref is an integer

returnType :: Type -> Type
returnType TNumber = TNumber
returnType t@(TArr _ _) = t
returnType (TAbs _ t) = t

peelType :: Type -> Int -> Type
peelType = undefined

paramTypes :: Type -> [Type]
paramTypes TNumber = error "paramTypes: number (this is a bug)"
paramTypes t@(TArr _ _) = error "paramTypes: array (this is a bug)"
paramTypes (TAbs ps _) = ps

data Number = I Int | F Double
  deriving Show

data Ident = Ident String
  deriving (Eq, Ord, Show)

data Index a = IdxConst Int | IdxVar a
  deriving (Show, Functor, Foldable, Traversable)

data Op = Plus | Minus | Mul | Div
  deriving Show

data Abs = Abs Type [Ident] {- bindings -} [(Ident, Expr)] Expr
  deriving Show

data Expr
  = EConst Number
  | EOp Op Expr Expr -- both args and the result are simple types
  | EArr Type [Expr]

  | EAbs Abs
  | EApp Type Ident [Expr]

  | EExtern Type Ident [Expr] -- can reference functions or shared mem

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

data SExpr idx
  = SConst Number
  | SArr Type [Expr]
  | SOp Op Expr Expr
  | SAbs Abs
  | SApp Type Ident [Expr]
  | SExtern Type Ident [Expr]
  deriving (Show)

data Choice idx
  = CChoice Type [Choice idx] idx
  | CExpr [(Type, Index Expr)] (SExpr idx) -- selection indices that flow into the inner expression
  deriving (Show)

toC :: Monad m => SExpr (Index Expr) -> StackM (Type, Index Expr) m (Choice (Index Expr))
toC e = do
  idxs <- ST.get
  pure $ CExpr idxs e

choiceTree :: Monad m => Expr -> StackM (Type, Index Expr) m (Choice (Index Expr))
choiceTree (EConst n) = toC (SConst n)
choiceTree (EOp op a b) = toC (SOp op a b)
choiceTree (EExtern t n es) = toC (SExtern t n es)
choiceTree (EApp t n es) = toC (SApp t n es)
choiceTree (EAbs abs) = toC (SAbs abs)
choiceTree (EArr t es) = do
  s <- pop
  case s of
    Just (t, idx) -> do
      es' <- traverse choiceTree es
      push (t, idx)
      pure $ CChoice t es' idx
    Nothing -> pure $ CExpr [] (SArr t es)
choiceTree (ESelect t e idx) = do
  push (t, idx)
  c <- choiceTree e
  _ <- pop
  pure c
choiceTree (ERec _ _ _ e) = choiceTree e -- TODO: need to inline ident with delay boxes

-- TODO: optimization, cluster generation and so on go here
elimConstIndices :: Choice (Index Expr) -> Choice Expr
elimConstIndices (CExpr idxs (SConst n)) = CExpr idxs (SConst n)
elimConstIndices (CExpr idxs (SApp t n es)) = CExpr idxs (SApp t n es)
elimConstIndices (CExpr idxs (SExtern t n es)) = CExpr idxs (SExtern t n es)
elimConstIndices (CExpr idxs (SArr t es)) = CExpr idxs (SArr t es)
elimConstIndices (CChoice _ chs (IdxConst idx)) = elimConstIndices (chs !! idx)
elimConstIndices (CChoice t chs (IdxVar idx)) = CChoice t (map elimConstIndices chs) idx

toChoice :: Expr -> Choice Expr
toChoice = elimConstIndices . flip ST.evalState [] . choiceTree

-- call ------------------------------------------------------------------------

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
