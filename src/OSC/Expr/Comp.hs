{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.Comp where

import Data.Comp
import Data.Comp.Derive
import Data.Comp.Ops
import Data.Comp.Term

import Control.Monad.State

data Value val = Const Int | Arr [val]
  deriving Functor

data Lam exp = Lam [String] [(String, exp)] exp
  deriving Functor

data Exp exp
  = Op exp exp
  | Var String
  | App exp [exp]
  | Select exp exp
  deriving Functor

data FuncRef exp = FuncRef Int
  deriving Functor

type Sig  = Exp :+: Value :+: Lam
type Sig' = Exp :+: Value :+: FuncRef

$(derive
    [ makeTraversable
    , makeFoldable
    , makeEqF
    , makeShowF
    , smartConstructors
    , smartAConstructors
    ]
    [''Value, ''Lam, ''Exp, ''FuncRef]
  )

class GatherAlg f where
  gatherAlg :: AlgM (State GatherState) f (Term Sig')

instance GatherAlg Lam where
  gatherAlg (Lam params locals body) = do
    funcId <- gets nextFuncId
    modify $ \s -> s { nextFuncId = nextFuncId s + 1 }
    modify $ \s -> s { collectedFuncs = (funcId, params, locals, body) : collectedFuncs s }
    return $ inject (FuncRef funcId)

instance (f :<: Sig') => GatherAlg f where
  gatherAlg = return . inject

instance (GatherAlg f, GatherAlg g) => GatherAlg (f :+: g) where
  gatherAlg (Inl x) = gatherAlg x
  gatherAlg (Inr x) = gatherAlg x

gatherAbs :: Term Sig -> Term Sig'
gatherAbs term = evalState (cataM gatherAlg term) initialState
  where
    initialState :: GatherState
    initialState = GatherState
      { nextFuncId = 0
      , collectedFuncs = []
      }

data GatherState = GatherState
  { nextFuncId :: Int
  , collectedFuncs :: [(Int, [String], [(String, Term Sig')], Term Sig')]
  }
