{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module OSC.Records where

import qualified Data.Map as M
import Data.Kind
import Data.Dynamic
import Data.Maybe (fromJust)
import Data.Proxy
import GHC.Records
import GHC.TypeLits
import GHC.OverloadedLabels

type family HasNot (target :: Symbol) (names :: [(Symbol, Type)]) :: Constraint where
  HasNot x '[] = ()
  HasNot x ('(x, v) ': ys) = TypeError ('Text "Field already declared: " ':<>: 'ShowType x)
  HasNot x ('(y, v) ': ys) = HasNot x ys

type family Has (target :: Symbol) (names :: [(Symbol, Type)]) :: Type where
  Has x '[] = TypeError ('Text "No field: " ':<>: 'ShowType x)
  Has x ('(x, v) ': ys) = v
  Has x ('(y, v) ': ys) = Has x ys

data Label (name :: Symbol) = Label

instance (l ~ x) => IsLabel l (Label x) where
  fromLabel = Label

data Record (fields :: [(Symbol, Type)]) = Record (M.Map String Dynamic)

type Extend (k :: Symbol) v r r' = (r' ~ '(k, v):r, HasNot k r)

empty :: Record '[]
empty = Record mempty

extend :: forall k v r. HasNot k r => KnownSymbol k => Typeable v => Label k -> v -> Record r -> Record ('(k, v):r)
extend _ v (Record m) = Record (M.insert (symbolVal @k Proxy) (toDyn v) m)

update :: forall k v r. Has k r ~ v => KnownSymbol k => Typeable v => Label k -> v -> Record r -> Record r
update _ v (Record m) = Record (M.insert (symbolVal @k Proxy) (toDyn v) m)

(=:) :: forall k v r. HasNot k r => KnownSymbol k => Typeable v => Label k -> v -> (Record r -> Record ('(k, v):r))
k =: v = extend k v

(~:) :: forall k v r. Has k r ~ v => KnownSymbol k => Typeable v => Label k -> v -> (Record r -> Record r)
k ~: v = update k v

instance (Has k r ~ v, KnownSymbol k, Typeable v) => HasField k (Record r) v where
  getField (Record m) = fromJust $ fromDynamic @v (m M.! (symbolVal @k Proxy))