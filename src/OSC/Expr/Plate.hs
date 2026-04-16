{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module OSC.Expr.Plate where

import Data.Functor.Identity (Identity (runIdentity))

data Empty exp

class Plate expr where
  descendM :: Monad m
    => (f expr -> m (expr (f expr)))  -- | Unrwap

    -> f expr
    -> m [f expr]

universe :: Plate expr => (f expr -> expr (f expr)) -> f expr -> [f expr]
universe unwrap expr = expr:((\children -> children <> concatMap (universe unwrap) children) $ runIdentity $ descendM (fmap pure unwrap) expr)

class BiPlate a b c | a c -> b, b c -> a, a b -> c where
  transformBiM :: Monad m
    => (f a -> m (a (f a)))   -- | Unwrap

    -> (b (f' b) -> m (f' b)) -- | Self transform
    -> (c (f' b) -> m (f' b)) -- | Diff transform

    -> f a
    -> m (f' b)

transformM :: Monad m => BiPlate a a Empty
  => (f a -> m (a (f a)))
  -> (a (f' a) -> m (f' a))
  -> f a
  -> m (f' a)
transformM unwrap f = transformBiM unwrap f undefined

transform :: BiPlate a a Empty
  => (f a -> a (f a))
  -> (a (f' a) -> f' a)
  -> f a
  -> f' a
transform unwrap f = runIdentity . transformBiM (fmap pure unwrap) (fmap pure f) undefined