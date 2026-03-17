{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
module OSC.Ctx where

import qualified Control.Monad.State as ST

import Data.Bifunctor (first, second)

data Type = TNumber | TArray Type Int -- dimension
  deriving Show

data Number = I Int | F Double
  deriving Show

data Ident = Ident String
  deriving (Eq, Ord, Show)

data Index a = IdxConst Int | IdxVar a
  deriving (Show, Functor, Foldable, Traversable)

data Expr
  = EConst Number
  | EEmbedGraph Type Expr [Expr]
  | ECall Type Ident [Expr]
  | EArr Type [Expr]
  | ESelect Type Expr (Index Expr)
  | ERec Type Int Ident Expr -- rec delay |prev| -> expr
  deriving Show

data FTree e r = FLeaf r | FArr [FTree e r] | FChoice (FTree e r) (Index e)

data R = RConst Number | RCall Ident [Expr] | REmbedGraph Ident [Expr]

-- insight: inner type of select must *at some point* be an array (unless copy-select)
-- external calls must be turned into copy-selects (e.g. alloc internal array, compute function, copy indexed elements to array ctx) and a slow code warning issued

-- recursive bindings are *always* computed (not sure if relevant here)

funcrefs :: (Ident -> Expr) -> Expr -> FTree Expr R
funcrefs _ (EConst n) = FLeaf (RConst n)
funcrefs _ (ECall _ n es) = FLeaf (RCall n es)
funcrefs env (EEmbedGraph _ n _) = funcrefs env (env n)
funcrefs env (EArr _ es) = FArr (map (funcrefs env) es)
funcrefs env (ESelect _ e idx) = FChoice (funcrefs env e) idx

--------------------------------------------------------------------------------

type StackM s m a = ST.StateT [s] m a

push :: s -> StackM s m ()
push = undefined

pop :: StackM s m ()
pop = undefined

modify :: (s -> s) -> StackM s m ()
modify = undefined

--------------------------------------------------------------------------------

-- can we pass the selection indices down an Embed subtree?

data N = N [N] | L Expr

data T = Rec N (Index Expr) | Embed T [Expr] | Call Ident [Expr]

frefs :: Expr -> StackM ([N], Index Expr) m (N -> N)
frefs (EArr _ es) = do
  modify (first _)
  pop
  pure id
frefs (ESelect _ e idx) = do
  Rec (frefs e) idx

-- array ctx -------------------------------------------------------------------

data AllocM a

at :: Int -> AllocM () -> AllocM ()
at = undefined

-- the type lets runArrayCtxM know how big of an array (or value) to allocate
runArrayCtxM :: Type -> ()
runArrayCtxM = undefined
