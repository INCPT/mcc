{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module OSC.Records where

import qualified Data.Map as M
import Data.Kind
import Data.Proxy
import GHC.Records
import GHC.TypeLits
import GHC.OverloadedLabels

import Unsafe.Coerce

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

data Any = forall a. Any a

toAny :: a -> Any
toAny = Any

fromAny :: Any -> a
fromAny (Any a) = unsafeCoerce a

data Record (fields :: [(Symbol, Type)]) = Record (M.Map String Any)

type Extend (k :: Symbol) v r r' = (r' ~ '(k, v):r, HasNot k r, Has k r' ~ v)

empty :: Record '[]
empty = Record mempty

singleton :: forall k v r. KnownSymbol k => Extend k v '[] r => Label k -> v -> Record r
singleton _ v = Record (M.singleton (symbolVal @k Proxy) (toAny v))

get :: forall k v r. Has k r ~ v => KnownSymbol k => Label k -> Record r -> v
get _ (Record m) = fromAny @v (m M.! (symbolVal @k Proxy))

extend :: forall k v r r'. KnownSymbol k => Extend k v r r' => Label k -> v -> Record r -> Record r'
extend _ v (Record m) = Record (M.insert (symbolVal @k Proxy) (toAny v) m)

update :: forall k v r. KnownSymbol k => Has k r ~ v => Label k -> v -> Record r -> Record r
update _ v (Record m) = Record (M.insert (symbolVal @k Proxy) (toAny v) m)

(=:) :: forall k v r. KnownSymbol k => HasNot k r => Label k -> v -> (Record r -> Record ('(k, v):r))
k =: v = extend k v

(~:) :: forall k v r. KnownSymbol k => Has k r ~ v => Label k -> v -> (Record r -> Record r)
k ~: v = update k v

instance (KnownSymbol k, Has k r ~ v) => HasField k (Record r) v where
  getField = get (Label @k)