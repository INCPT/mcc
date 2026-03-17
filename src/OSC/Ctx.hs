{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
module OSC.Ctx where

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
  | EEmbedGraph Type Ident [Expr]
  | EVar Type Ident
  | EArr Type [Expr]
  | ESelect Type Expr (Index Expr)
  | ERec Type Int Ident Expr -- rec delay |prev| -> expr
  | ECall Type Ident [Expr]
  deriving Show

data FTree e r = FLeaf r | FArr [FTree e r] | FChoice (FTree e r) (Index e)

data R = RConst Number | RCall Ident [Expr] | REmbedGraph Ident [Expr]

-- insight: inner type of select must *at some point* be an array
-- external calls must be turned into copy-selects (e.g. alloc internal array, compute function, copy indexed elements to array ctx) and a slow code warning issued
-- recursive bindings are *always* computed

funcrefs :: (Ident -> Expr) -> Expr -> FTree Expr R
funcrefs _ (EConst n) = FLeaf (RConst n)
funcrefs _ (ECall _ n es) = FLeaf (RCall n es)
funcrefs _ (EVar _ n) = FLeaf (RCall n [])
funcrefs env (EEmbedGraph _ n _) = funcrefs env (env n)
funcrefs env (EArr _ es) = FArr (map (funcrefs env) es)
funcrefs env (ESelect _ e idx) = FChoice (funcrefs env e) idx

-- array ctx:

data AllocM a

at :: Int -> AllocM () -> AllocM ()
at = undefined

-- the type lets runArrayCtxM know how big of an array (or value) to allocate
runArrayCtxM :: Type -> ()
runArrayCtxM = undefined
