{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}

module OSC.Ctx where

import Control.Applicative ((<|>))
import Data.Functor.Identity
import Control.Monad.Trans (MonadTrans, lift)
import qualified Control.Monad.Reader as R
import qualified Control.Monad.State as ST
import qualified Data.Map as M

data Type = TNumber | TArray Type {- length -} Int | TAbs [(Ident, Type)] Type
  deriving Show

data Number = I Int | F Double
  deriving Show

data Ident = Ident String
  deriving (Eq, Ord, Show)

data Index a = IdxConst Int | IdxVar a
  deriving (Show, Functor, Foldable, Traversable)

data Op = Plus | Minus | Mul | Div
  deriving Show

data Abs = Abs Type [(Ident, Type)] {- bindings -} [(Ident, Expr)] Expr
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
  | SOp Op Expr Expr
  | SArr [Choice idx]
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
choiceTree (EArr _ es) = do
  s <- pop
  case s of
    Just (t, idx) -> do
      es' <- traverse choiceTree es
      push (t, idx)
      pure $ CChoice t es' idx
    Nothing -> do
      ces <- traverse choiceTree es
      pure $ CExpr [] (SArr ces)
choiceTree (ESelect t e idx) = do
  push (t, idx)
  c <- choiceTree e
  _ <- pop
  pure c
choiceTree (ERec _ _ _ e) = choiceTree e -- TODO: need to inline ident with delay boxes

elimConstIndices :: Choice (Index Expr) -> Choice Expr
elimConstIndices (CExpr idxs (SConst n)) = CExpr idxs (SConst n)
elimConstIndices (CExpr idxs (SApp t n es)) = CExpr idxs (SApp t n es)
elimConstIndices (CExpr idxs (SExtern t n es)) = CExpr idxs (SExtern t n es)
elimConstIndices (CExpr idxs (SArr es)) = CExpr idxs (SArr $ map elimConstIndices es)
elimConstIndices (CChoice _ chs (IdxConst idx)) = elimConstIndices (chs !! idx)
elimConstIndices (CChoice t chs (IdxVar idx)) = CChoice t (map elimConstIndices chs) idx

-- array ctx -------------------------------------------------------------------

newtype AllocM m a = AllocM (ST.StateT () m a)
  deriving (Functor, Applicative, Monad, MonadTrans)

data FuncRef

data Value = RConst Number | RLocal Int | RArray Int

sizeOfType :: Type -> Int
sizeOfType TNumber = 4
sizeOfType (TArray t dim) = sizeOfType t * dim
sizeOfType (TAbs _ _) = 4 -- funcref is an integer

-- TODO: optimization is performed on the Choice datatype

-- TODO: alignment in AllocM!

-- TODO: what happens if part of the return value is a capture?
-- this is basically return value ref propagation up the binding chain
-- the most recent returned binding (or argument) gets tagged with "write to return value ref"

-- type is needed for type signature in WASM/C
funcRef :: Monad m => Type -> AllocM m () -> AllocM m FuncRef
funcRef = undefined

alloc :: Type -> AllocM m a -> AllocM m (a, Value)
alloc = undefined

at :: Int -> AllocM m () -> AllocM m ()
at = undefined

ret :: Number -> AllocM m ()
ret = undefined

call :: FuncRef -> [Value] -> AllocM m Value
call = undefined

data Env = Env
  { globalAbs :: M.Map Ident Abs
  , localBindings :: M.Map Ident Expr
  }

toAbs :: Expr -> Maybe Abs
toAbs = undefined

allocExpr :: SExpr Expr -> AllocM (R.Reader Env) ()
allocExpr (SConst n) = ret n
allocExpr (SExtern _ _ _) = undefined
allocExpr (SApp _ n args) = do
  env <- lift R.ask
  case M.lookup n env.globalAbs <|> (M.lookup n env.localBindings >>= toAbs) of
    Just (Abs t params bindings e) -> undefined
    Nothing -> error "allocExpr: app: no binding in scope (this is a bug)"
allocExpr (SArr es) = sequence_ [ at i $ allocChoice e | (i, e) <- zip [0..] es ]

allocChoice :: Monad m => Choice Expr -> AllocM m ()
allocChoice (CExpr _ e) = allocExpr e

--------------------------------------------------------------------------------

t :: [Int] -> Type
t [] = TNumber
t (dim:dims) = TArray (t dims) dim

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
