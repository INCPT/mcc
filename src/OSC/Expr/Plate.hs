{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module OSC.Expr.Plate where

import Data.Foldable (foldl)
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

type Unwrap f = forall a. f a -> a (f a)

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

--------------------------------------------------------------------------------

type Alg expr f = expr f -> f

-- this is transformM
cata :: Functor expr => Unwrap f -> Alg expr g -> f expr -> g
cata unwrap f = f . fmap (cata unwrap f) . unwrap
-- cata unwrap f = c where c = f . fmap c . unwrap

embed :: expr (f expr) -> (f expr)
embed = undefined

query :: Foldable expr => Unwrap f -> (f expr -> r) -> (r -> r -> r) -> f expr -> r
query unwrap q c t = foldl (\r x -> r `c` query unwrap q c x) (q t) (unwrap t)

subs' :: Foldable expr => Unwrap f -> f expr -> [f expr]
subs' unwrap = query unwrap pure (<>)

subs :: Foldable expr => Unwrap f -> f expr -> [expr (f expr)]
subs unwrap = fmap unwrap . query unwrap pure (<>)
