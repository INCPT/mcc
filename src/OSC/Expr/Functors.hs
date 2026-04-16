{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}

module OSC.Expr.Functors where

import Control.Monad.Identity (Identity(..))
import qualified Control.Monad.Reader as R
import qualified Control.Monad.State as ST

class Wrap f where
  wrap :: exp (f exp) -> f exp

class WFunctor f where
  wmapM :: Functor m => (exp (f exp) -> m (exp (f exp))) -> f exp -> m (f exp)

-- Simple recursive type
newtype Fix f = Fix { unFix :: f (Fix f) }

deriving instance Show (f (Fix f)) => Show (Fix f)

instance Wrap Fix where
  wrap = Fix

instance WFunctor Fix where
  wmapM g (Fix f) = Fix <$> g f

-- Annotated recursive type + monad
newtype Ann ann f = Ann { unAnn :: (ann, f (Ann ann f)) }
newtype AnnM ann a = AnnM ((a -> ann) -> ann)

deriving instance (Show ann, Show (f (Ann ann f))) => Show (Ann ann f)

instance Monoid ann => Wrap (Ann ann) where
  wrap a = Ann (mempty, a)

instance WFunctor (Ann ann) where
  wmapM g (Ann (ann, f)) = Ann <$> ((ann,) <$> g f)

unwrapAnn :: Ann ann f -> AnnM ann (f (Ann ann f))
unwrapAnn (Ann (ann, _)) = AnnM $ \_ -> ann

wrapAnn :: f (Ann ann f) -> AnnM ann (Ann ann f)
wrapAnn f = AnnM $ \k -> let ann = k (Ann (ann, f)) in ann

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

-- RecursiveWrapper instances --------------------------------------------------

-- Helper newtype for Dag's resolver that hides the expr parameter
newtype DagResolver k = DagResolver { runDagResolver :: forall expr. k -> Dag k expr }

class RecursiveWrapper f where
  type WrapContext f :: * -> *
  runwrap :: Functor expr => f expr -> WrapContext f (expr (f expr))
  rwrap :: (expr (f expr) -> expr (f expr)) -> f expr -> f expr

instance RecursiveWrapper Fix where
  type WrapContext Fix = Identity
  runwrap (Fix f) = Identity f
  rwrap modify (Fix f) = Fix (modify f)

instance RecursiveWrapper (Ann ann) where
  type WrapContext (Ann ann) = Identity
  runwrap (Ann (ann, f)) = Identity f
  rwrap modify (Ann (ann, f)) = Ann (ann, modify f)

instance RecursiveWrapper (Dag k) where
  type WrapContext (Dag k) = R.Reader (DagResolver k)
  runwrap (Node f) = return f
  runwrap (Key k) = do
    DagResolver resolve <- R.ask
    runwrap (resolve k)
  rwrap modify (Node f) = Node (modify f)
  rwrap modify (Key k) = Key k

-- Higher order variants -------------------------------------------------------

data AnnF ann f r = AnnF ann (f r)

data DagF k f r = NodeF (f r) | KeyF k

-- can be composed like this:

-- type AnnDag ann k expr = Fix (AnnF ann (DagF k expr))
