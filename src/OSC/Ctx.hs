{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}

module OSC.Ctx where

import Data.Functor.Identity
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

push :: Monad m => s -> StackM s m ()
push s = ST.modify (s:)

pop :: Monad m => StackM s m s
pop = do
  as <- ST.get
  case as of
    (a:as) -> do
      ST.put as
      pure a

modify :: Monad m => (s -> s) -> StackM s m ()
modify f = ST.modify $ \st -> case st of
  (a:as) -> (f a:as)

runStack :: StackM s Identity a -> a
runStack = flip ST.evalState []

--------------------------------------------------------------------------------

-- can we pass the selection indices down an Embed subtree?

data Choice = CChoice [(Int, Choice)] (Index Expr) | CExpr Expr
  deriving (Show)

frefs :: Monad m => Expr -> StackM (Index Expr) m Choice
frefs e@(EConst _) = pure $ CExpr e
frefs e@(ECall _ _ _) = pure $ CExpr e
frefs e@(EEmbed _ _ _) = pure $ CExpr e
frefs (EArr _ es) = do
  idx <- pop
  es' <- traverse frefs es
  pure $ CChoice [ (i, e) | (i, e) <- zip [0..] es' ] idx
frefs (ESelect _ e idx) = do
  push idx
  frefs e
frefs (ERec _ _ _ e) = frefs e

-- array ctx -------------------------------------------------------------------

data AllocM a

at :: Int -> AllocM () -> AllocM ()
at = undefined

-- the type lets runArrayCtxM know how big of an array (or value) to allocate
runArrayCtxM :: Type -> ()
runArrayCtxM = undefined

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

