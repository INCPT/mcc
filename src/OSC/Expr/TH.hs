{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module OSC.Expr.TH where

import Control.Monad.Trans

-- Pair a recursive functor with a lookup monad
class Lookup mu m where
  unwrap :: Applicative m => mu expr -> m (expr (mu expr))

class Plate expr where
  descend :: Lookup mu m => Monad m => (mu expr -> expr (mu expr) -> m (Maybe a)) -> mu expr -> m [a]
  transform :: Lookup mu m => Monad m => (expr (mu expr) -> m (expr (mu expr))) -> mu expr -> m (expr (mu expr))

class BiPlate a b diff | a b -> diff, a diff -> b, b diff -> a where
  transformBi :: Lookup mu m => Monad m => (diff (mu diff) -> m (b (mu b))) -> a (mu a) -> m (b (mu b))

--------------------------------------------------------------------------------

-- Recursive functor
data Mu f = Mu (f (Mu f))

-- Lookup monad
data AnnM m ann mu expr = AnnM (ann -> expr (mu expr) -> m (ann, expr (mu expr)))

instance Applicative f => Lookup Mu f where
  unwrap (Mu f) = pure f

-- write a TH function that:

---- having the following types

data Value exp = Const Int | Arr [exp]
data Expr exp = Add exp exp | Mul exp exp

---- and calling

------ makeSum "S_" "Sum0" [''Value, ''Expr]

---- will generate the following datatype:

data Sum0 exp
  = S_Const Int
  | S_Arr [exp]
  | S_Add exp exp
  | S_Mul exp exp
  deriving (Functor, Foldable, Traversable)

---- and implement the Plate class:

instance Plate Sum0 where
  descend extract expr = do
    undefined
    -- inner <- unwrap expr
    -- a <- extract expr inner
    -- case a of
    --   Just a' -> pure [a']
    --   Nothing -> case inner of
    --     S_Const _ -> pure []
    --     -- if field is of type `h (g (f exp)) ...` (like `[exp]` or `[Maybe exp]`) then just traverse (not sure if mconcat etc is needed for more complicated traversls) - we'll throw a type error if f isn't a Traversable
    --     S_Arr exprs -> fmap mconcat $ traverse (descend extract) exprs
    --     S_Add exp1 exp2 -> (<>) <$> descend extract exp1 <*> descend extract exp2
    --     S_Mul exp1 exp2 -> (<>) <$> descend extract exp1 <*> descend extract exp2

  transform f expr = undefined
    -- inner <- pure $ unwrap expr
    -- case inner of
    --   S_Const n -> (S_Const <$> pure n)
    --   _ -> undefined
    --   -- S_Arr exprs -> fmap wrap (S_Arr <$> traverse (transform f) exprs)
    --   -- S_Add exp1 exp2 -> fmap wrap ()
  
---- calling

------ makeDiff "D_" "Sum0_Expr" [''Value, ''Expr] [''Value]

---- will generate the following datatype:

data Sum0_Expr exp
  = D_Add exp exp
  | D_Mul exp exp

---- and implement the BiPlate class:

-- instance BiPlate Sum0 Expr Sum0_Expr where
--   transformBi a b = undefined