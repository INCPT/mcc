{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}

module OSC.Expr.Functors where

import OSC.Expr.Plate (Wrap (wrap))

import qualified Control.Monad.Reader as R

-- Simple recursive type
newtype Fix f = Fix { unFix :: f (Fix f) }

deriving instance Show (f (Fix f)) => Show (Fix f)

instance Wrap Fix where
  wrap = Fix

-- Annotated recursive type + monad
newtype Ann ann f = Ann { unAnn :: (ann, f (Ann ann f)) }
type AnnM = R.ReaderT

deriving instance (Show ann, Show (f (Ann ann f))) => Show (Ann ann f)

instance Monoid ann => Wrap (Ann ann) where
  wrap a = Ann (mempty, a)

flowAnn :: Monad m => (ann -> ann') -> AnnM ann m (exp (Ann ann' exp)) -> AnnM ann m (Ann ann' exp)
flowAnn f m = R.ask >>= \ann -> Ann <$> (f ann,) <$> m

hoistAnn :: Functor f => (ann -> ann') -> Ann ann f -> Ann ann' f
hoistAnn h (Ann (ann, f)) = Ann (h ann, fmap (hoistAnn h) f)

hoistAnnM :: Traversable f => Monad m => (ann -> m ann') -> Ann ann f -> m (Ann ann' f)
hoistAnnM h (Ann (ann, f)) = Ann <$> ((,) <$> h ann <*> traverse (hoistAnnM h) f)

fixToAnn :: Functor f => Monoid pos => Fix f -> Ann pos f
fixToAnn (Fix f) = Ann (mempty, fmap fixToAnn f)

fixToAnn' :: Functor f => Fix f -> Ann () f
fixToAnn' (Fix f) = Ann (mempty, fmap fixToAnn' f)

annToFix :: Functor f => Ann ann f -> Fix f
annToFix (Ann (_, f)) = Fix (fmap annToFix f)

-- DAG recursive type + monad
data Dag k f = Node (f (Dag k f)) | Key k
type DagM k expr = R.Reader (k -> expr (Dag k expr))

deriving instance (Show k, Show (f (Dag k f))) => Show (Dag k f)

instance Wrap (Dag k) where
  wrap = Node

-- Higher order variants -------------------------------------------------------

data AnnF ann f r = AnnF ann (f r)

data DagF k f r = NodeF (f r) | KeyF k

-- can be composed like this:

-- type AnnDag ann k expr = Fix (AnnF ann (DagF k expr))