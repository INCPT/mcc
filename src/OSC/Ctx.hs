{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}

module OSC.Ctx where

import qualified Control.Monad.State as ST

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
  | EEmbed Type Expr [Expr]
  | ECall Type Ident [Expr]
  | EArr Type [Expr]
  | ESelect Type Expr (Index Expr)
  | ERec Type Int Ident Expr -- rec delay |prev| -> expr
  deriving Show

--------------------------------------------------------------------------------

type StackM s m a = ST.StateT [s] m a

push :: s -> StackM s m ()
push = undefined

pop :: StackM s m s
pop = undefined

modify :: (s -> s) -> StackM s m ()
modify = undefined

--------------------------------------------------------------------------------

-- can we pass the selection indices down an Embed subtree?

data Choice = CChoice [(Int, Choice)] (Index Expr) | CExpr Expr

frefs :: Monad m => Expr -> StackM (Index Expr) m Choice
frefs e@(EConst _) = pure $ CExpr e
frefs e@(ECall _ _ _) = pure $ CExpr e
frefs e@(EEmbed _ _ _) = pure $ CExpr e
frefs (EArr _ es) = do
  idx <- pop
  es' <- traverse frefs es
  pure $ CChoice [ (i, e) | (i, e) <- zip [0..] es' ] idx
frefs (ESelect _ e _) = frefs e
frefs (ERec _ _ _ e) = frefs e

-- array ctx -------------------------------------------------------------------

data AllocM a

at :: Int -> AllocM () -> AllocM ()
at = undefined

-- the type lets runArrayCtxM know how big of an array (or value) to allocate
runArrayCtxM :: Type -> ()
runArrayCtxM = undefined
