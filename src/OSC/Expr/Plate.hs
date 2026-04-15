{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module OSC.Expr.Plate where

import Data.Functor.Identity (Identity (runIdentity))

data Empty exp

class Wrap f where
  wrap :: exp (f exp) -> f exp

class Plate expr where
  descend :: Monad m
    => (f expr -> m (expr (f expr)))  -- | Unrwap

    -> f expr
    -> m [f expr]

universe :: Plate expr => (f expr -> expr (f expr)) -> f expr -> [f expr]
universe unwrap expr = expr:((\children -> children <> concatMap (universe unwrap) children) $ runIdentity $ descend (fmap pure unwrap) expr)

class BiPlate a b c | a c -> b, b c -> a, a b -> c where
  transformBi :: Monad m
    => (f a -> m (a (f a)))   -- | Unwrap
    -> (b (f' b) -> m (f' b)) -- | Wrap

    -> (c (f' b) -> m (f' b)) -- | Transform

    -> f a
    -> m (f' b)
  
transform :: Monad m => BiPlate a a Empty
  => (f a -> m (a (f a)))
  -> (a (f' a) -> m (f' a))
  -> f a
  -> m (f' a)
transform unwrap f = transformBi unwrap f undefined