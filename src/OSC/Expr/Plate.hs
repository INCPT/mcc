{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module OSC.Expr.Plate where

data Empty exp

class BiPlate a b c | a c -> b, b c -> a, a b -> c where
  transformBiM :: Monad m
    => (f a -> m (a (f a)))   -- | Unwrap

    -> (b (f' b) -> m (f' b)) -- | Self transform
    -> (c (f' b) -> m (f' b)) -- | Diff transform

    -> f a
    -> m (f' b)

class Bitraversable a b c | a c -> b, b c -> a, a b -> c where
  bitraverse
    :: Monad m
    => (f a -> m (f' b))

    -> (c (f a) -> m (b (f' b)))
    -> a (f a)
    -> m (b (f' b))