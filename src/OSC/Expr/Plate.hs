{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module OSC.Expr.Plate where

import OSC.Expr.Functors
import Data.Foldable (foldl)
import Data.Functor.Identity (Identity (runIdentity))

data Empty exp

class BiPlate a b c | a c -> b, b c -> a, a b -> c where
  transformBiM :: Monad m
    => (f a -> m (a (f a)))   -- | Unwrap

    -> (b (f' b) -> m (f' b)) -- | Self transform
    -> (c (f' b) -> m (f' b)) -- | Diff transform

    -> f a
    -> m (f' b)

class TraversableBi a b c | a c -> b, b c -> a, a b -> c where
  traverseBi
    :: Monad m
    => (f a -> m (f' b))

    -> (c (f' b) -> m (b (f' b)))
    -> a (f a)
    -> m (b (f' b))
  traverseBi = undefined

class RecPlate a where
  transformRec :: Monad m => BiPlate a a Empty
    => (f a -> m (f' a))
    -> a (f a) -> m (a (f' a))
  transformRec wmap f = undefined

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