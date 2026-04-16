{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}

module OSC.Expr.Functors where

import Data.Functor.Identity (runIdentity)

import qualified Control.Monad.Reader as R

class Corecursive f where
  embed :: a (f a) -> f a

class Recursive f where
  project :: f a -> a (f a)

class RFunctor f where
  rtraverse :: Functor m => (a (f a) -> m (b (f b))) -> f a -> m (f b)

hoist :: Recursive f => Corecursive g => Functor a => f a -> g a
hoist = embed . fmap hoist . project

-- Fix -------------------------------------------------------------------------

newtype Fix f = Fix { unFix :: f (Fix f) }

deriving instance Show (f (Fix f)) => Show (Fix f)

instance Recursive Fix where project = unFix
instance Corecursive Fix where embed = Fix
instance RFunctor Fix where rtraverse g (Fix f) = Fix <$> g f

-- Ann -------------------------------------------------------------------------

newtype Ann ann f = Ann { unAnn :: (ann, f (Ann ann f)) }

deriving instance (Show ann, Show (f (Ann ann f))) => Show (Ann ann f)

instance Recursive (Ann ann) where project = snd . unAnn
instance Monoid ann => Corecursive (Ann ann) where embed a = Ann (mempty, a)
instance RFunctor (Ann ann) where rtraverse g (Ann (ann, f)) = Ann <$> ((ann,) <$> g f)

mapAnnM :: Traversable f => Monad m => (ann -> m ann') -> Ann ann f -> m (Ann ann' f)
mapAnnM h (Ann (ann, f)) = Ann <$> ((,) <$> h ann <*> traverse (mapAnnM h) f)

mapAnn :: Traversable f => Functor f => (ann -> ann') -> Ann ann f -> Ann ann' f
mapAnn h = runIdentity . mapAnnM (fmap pure h)

-- Ann -------------------------------------------------------------------------

data Dag k f = Node (f (Dag k f)) | Key k
type DagM k expr = R.Reader (k -> expr (Dag k expr))

deriving instance (Show k, Show (f (Dag k f))) => Show (Dag k f)

instance Corecursive (Dag k) where embed = Node

-- Higher order variants -------------------------------------------------------

data AnnF ann r f = AnnF ann (f r)

data DagF k f r = NodeF (f r) | KeyF k

-- can be composed like this:

-- type AnnDag ann k expr = Fix (AnnF ann (DagF k expr))

--------------------------------------------------------------------------------

type Alg expr f = expr f -> f

cata :: Functor expr => Recursive f => Alg expr g -> f expr -> g
cata f = f . fmap (cata f) . project
-- cata f = c where c = f . fmap c . project

query :: Foldable expr => Recursive f => (f expr -> r) -> (r -> r -> r) -> f expr -> r
query q c t = foldl (\r x -> r `c` query q c x) (q t) (project t)

universe' :: Foldable expr => Recursive f => f expr -> [f expr]
universe' = query pure (<>)

universe :: Foldable expr => Recursive f => f expr -> [expr (f expr)]
universe = fmap project . query pure (<>)