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

-- * TODO: in typechecking, check that static indices are within range
-- ** even better: attach range to index; then check if everything ok in range check
-- ***  otherwise expect a clamp() or wrap() range correcting fun
-- ** if not possible, then demand clamp/wrap in dynamic select index expressions
-- * TODO: in the CallM monad, arguments that get written to the output can pass their array ctx slice to the argument expression, so no need for copy

data Choice idx
  = CChoice Type [Choice idx] idx
  | CExpr [(Type, Index Expr)] Expr -- selection indices that flow into the inner expression
  deriving (Show)

toC :: Monad m => Expr -> StackM (Type, Index Expr) m (Choice (Index Expr))
toC e = do
  idxs <- ST.get
  pure $ CExpr idxs e

choiceTree :: Monad m => Expr -> StackM (Type, Index Expr) m (Choice (Index Expr))
choiceTree e@(EConst _) = toC e
choiceTree e@(ECall _ _ _) = toC e
choiceTree e@(EEmbed _ _ _) = toC e
choiceTree (EArr _ es) = do
  (t, idx) <- peek
  es' <- traverse choiceTree es
  pure $ CChoice t es' idx
choiceTree (ESelect t e idx) = do
  push (t, idx)
  c <- choiceTree e
  _ <- pop
  pure c
choiceTree (ERec _ _ _ e) = choiceTree e -- TODO: need to inline ident with delay boxes

elimConstIndices :: Choice (Index Expr) -> Choice Expr
elimConstIndices (CExpr idxs e) = CExpr idxs e
elimConstIndices (CChoice _ chs (IdxConst idx)) = elimConstIndices (chs !! idx)
elimConstIndices (CChoice t chs (IdxVar idx)) = CChoice t (map elimConstIndices chs) idx

-- array ctx -------------------------------------------------------------------

data AllocM a

data FuncRef

data Ref
data Ret

-- TODO: what happens if part of the return value is a capture?
-- this is basically return value ref propagation up the binding chain
-- the most recent returned binding (or argument) gets tagged with "write to return value ref"

-- fn allocs the return array
-- how are rvalues selected?
fn :: [(Ident, Type)] -> Type -> AllocM Ret -> AllocM FuncRef
fn = undefined

at :: Int -> AllocM () -> AllocM ()
at = undefined

binding :: Ident -> AllocM () -> AllocM ()
binding = undefined

capture :: Ident -> AllocM Ref
capture = undefined

call :: FuncRef -> [Ref] -> AllocM ()
call = undefined

layout :: Choice Expr -> AllocM ()
layout = undefined

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
