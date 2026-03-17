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

data FTree e = FLeaf e | FChoice [FTree e] e

funcrefs :: Expr -> FTree Expr
funcrefs e@(EConst _) = FLeaf e
funcrefs e@(ECall _ _ _) = FLeaf e
-- funcrefs (EArr _ es) = FArr (map funcrefs es)
-- funcrefs (ESelect _ (EArr _ es) (IdxVar idx)) = FChoice (fmap funcrefs es) (funcrefs idx)
-- funcrefs (ESelect _ e (IdxVar idx)) = FChoice [funcrefs e] (funcrefs idx)

-- array ctx:

data AllocM a

at :: Int -> AllocM () -> AllocM ()
at = undefined

-- the type lets runArrayCtxM know how big of an array (or value) to allocate
runArrayCtxM :: Type -> ()
runArrayCtxM = undefined
