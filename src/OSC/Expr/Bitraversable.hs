{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module OSC.Expr.Bitraversable where

import OSC.Expr.Functors

class Bitraversable a b c | a c -> b, b c -> a, a b -> c where
  bitraverse
    :: Monad m
    => (f a -> m (f' b))         -- | Traversal
    -> (c (f a) -> m (b (f' b))) -- | Differnce projection

    -> a (f a)
    -> m (b (f' b))
  
class Partition source dest diff part where
  partition 
    :: RFunctor2 f f' => Monad m
    => (diff (f source) -> m (dest (f' dest)))
    -> (part (f source) -> m (dest (f' dest)))
    -> f source -> m (f' dest)