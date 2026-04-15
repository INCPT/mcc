{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module OSC.Expr.Plate where

data Empty exp

class Plate expr where
  descend :: Monad m
    => (f expr -> m (expr (f expr)))   -- | Unrwap
 
    -> (expr (f expr) -> m (Maybe a))  -- | Gather

    -> f expr
    -> m [a]

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