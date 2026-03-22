{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TupleSections #-}

module OSC.Ctx where

import Control.Applicative ((<|>))
import Data.Functor.Identity
import Control.Monad.Trans (lift)
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

-- type is needed for type signature in WASM/C
funcRef :: FuncRef -> Type -> ([Ref] -> Ref -> AllocM ()) -> AllocM ()
funcRef = undefined

allocFuncRef :: AllocM FuncRef
allocFuncRef = undefined

allocArray :: Type -> AllocM ArrayRef
allocArray = undefined

data LocalType = LTNumber | LTFuncRef [Type]

allocLocal :: LocalType -> AllocM LocalRef
allocLocal = undefined

-- slice must be focused on a simple element here
writeArray :: ArrayRef -> Slice -> Number -> AllocM ()
writeArray = undefined

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

allocRef :: Type -> AllocM Ref
allocRef TNumber = RLocal <$> allocLocal LTNumber
allocRef t@(TArr _ _) = RArr (newSlice t) <$> allocArray t
allocRef (TAbs _ _) = RFuncRef <$> allocFuncRef

-- TODO: take spillover selection indices into account
allocExpr :: Ref -> SExpr Expr -> R.ReaderT Env AllocM ()
allocExpr (RLocal ref) (SConst n) = lift $ writeLocal ref n
allocExpr (RArr slice ref) (SConst n) = lift $ writeArray ref slice n
allocExpr (RArr slice ref) (SArr _ es) = sequence_
  [ allocChoice (RArr (focusSlice i slice) ref) (toChoice e)
  | (i, e) <- zip [0..] es
  ]
allocExpr (RLocal ref) (SOp op a b) = do
  aref <- lift $ allocLocal LTNumber
  bref <- lift $ allocLocal LTNumber
  allocChoice (RLocal aref) (toChoice a)
  allocChoice (RLocal bref) (toChoice b)
  lift $ callOp op aref bref ref
allocExpr ref (SExtern _ _ _) = undefined
allocExpr (RFuncRef fref) (SAbs (Abs t ns bindings e)) = mdo
  env <- R.ask

  bindingRefs <- fmap (M.fromList . mconcat) $ sequence
    [ case exprType bexpr of
        t@(TAbs _ _) -> do
          -- TODO: inline args in (toChoice bexpr)
          fr <- lift allocFuncRef
          lift $ funcRef fr t $ \args ref -> R.runReaderT (allocChoice ref (toChoice bexpr)) $ env
            { refs = bindingRefs `M.union` env.refs }

          pure [(bname, (t, RFuncRef fr))]
        t -> do
          ref <- lift $ allocRef t
          pure [(bname, (t, ref))]
    | (bname, bexpr) <- bindings
    ]

  -- TODO: inline bindingRefs in toChoice expr
  lift $ funcRef fref t $ \args ref -> R.runReaderT (allocChoice ref (toChoice e)) $ env
    { refs = bindingRefs `M.union` env.refs }
allocExpr ref (SApp _ n args) = do
  env <- R.ask

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
        [] -> lift $ call fr argRefs ref

        params' -> lift $ do
          case ref of
            RFuncRef curriedFr -> 
              funcRef curriedFr (TAbs params' (returnType t)) $ \curriedArgRefs ref' ->
                call fr (argRefs <> curriedArgRefs) ref'
            ref' ->  error $ "allocExpr: SApp: ref: " <> show ref' <> " (this is a bug)"
    e -> error $ "allocExpr: SApp: " <> show e <> " (this is a bug)"

allocChoice :: Ref -> Choice Expr -> R.ReaderT Env AllocM ()
allocChoice ref (CExpr _ e) = allocExpr ref e

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
