{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module OSC.Expr.Bitraversable where

class Bitraversable a b c | a c -> b, b c -> a, a b -> c where
  bitraverse
    :: Monad m
    => (f a -> m (f' b))         -- | Traversal
    -> (c (f a) -> m (b (f' b))) -- | Differnce projection

    -> a (f a)
    -> m (b (f' b))
  
class Partition source dest diff part where
  partition 
    :: Monad m
    => (forall a b. (a (f a) -> m (b (f' b))) -> f a -> m (f' b))

    -> (diff (f source) -> m (dest (f' dest)))
    -> (part (f source) -> m (dest (f' dest)))
    -> f source -> m (f' dest)