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

peek :: Monad m => StackM s m s
peek = do
  as <- ST.get
  case as of
    (a:as) -> pure a

modify :: Monad m => (s -> s) -> StackM s m ()
modify f = ST.modify $ \st -> case st of
  (a:as) -> (f a:as)

runStack :: StackM s Identity a -> a
runStack = flip ST.evalState []

--------------------------------------------------------------------------------

-- TODO: in the CallM monad, arguments that get written to the output can pass their array ctx slice to the argument expression, so no need for copy

data Choice
  = CChoice [(Int, Choice)] (Index Expr)
  | CExpr [Index Expr] Expr -- selection indices that flow into the inner expression
  deriving (Show)

frefs :: Monad m => Expr -> StackM (Index Expr) m Choice
frefs e@(EConst _) = pure $ CExpr [] e
frefs e@(ECall _ _ _) = pure $ CExpr [] e
frefs e@(EEmbed _ _ _) = do
  idxs <- ST.get
  pure $ CExpr idxs e
frefs (EArr _ es) = do
  idx <- pop
  es' <- traverse frefs es
  push idx
  pure $ CChoice [ (i, e) | (i, e) <- zip [0..] es' ] idx
frefs (ESelect _ e idx) = do
  push idx
  c <- frefs e
  _ <- pop
  pure c
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


e2 :: Expr
e2 = ESelect (t [3, 2]) (
  ESelect (t [2]) (
      EArr (t [3])
        [ (EArr (t [2]) [EConst $ I 0, EConst $ I 1])
        , (ECall (t [2]) (Ident "global") [])
        , (EArr (t [2]) [EConst $ I 4, EConst $ I 5])
        ])
    (IdxConst 2))
  (IdxConst 1)
