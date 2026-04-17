{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module OSC.Expr.Bitraversable where

class Bitraversable a b c | a c -> b, b c -> a, a b -> c where
  bitraverse
    :: Monad m
    => (f a -> m (f' b))         -- | Traversal
    -> (c (f a) -> m (b (f' b))) -- | Differnce projection

    -> a (f a)
    -> m (b (f' b))