{-# LANGUAGE TupleSections #-}

module OSC.Expr.Functors where

import OSC.Expr.Plate (Wrap (wrap))

import qualified Control.Monad.Reader as R

-- Simple recursive functor (can be paired with Identity)
newtype Fix f = Fix { unFix :: f (Fix f) }

instance Wrap Fix where
  wrap = Fix

-- Annotated recursive functor + monad
newtype Ann ann f = Ann { unAnn :: (ann, f (Ann ann f)) }
type AnnM = R.ReaderT

instance Monoid ann => Wrap (Ann ann) where
  wrap a = Ann (mempty, a)

hoistAnn :: Functor f => (ann -> ann') -> Ann ann f -> Ann ann' f
hoistAnn h (Ann (ann, f)) = Ann (h ann, fmap (hoistAnn h) f)

hoistAnnM :: Traversable f => Monad m => (ann -> m ann') -> Ann ann f -> m (Ann ann' f)
hoistAnnM h (Ann (ann, f)) = Ann <$> ((,) <$> h ann <*> traverse (hoistAnnM h) f)

flowAnn :: Monad m => (ann -> ann') -> AnnM ann m (exp (Ann ann' exp)) -> AnnM ann m (Ann ann' exp)
flowAnn f m = R.ask >>= \ann -> Ann <$> (f ann,) <$> m

-- DAG recursive functor + monad
data Dag k f = Node (f (Dag k f)) | Key k
type DagM k expr = R.Reader (k -> expr (Dag k expr))

instance Wrap (Dag k) where
  wrap = Node