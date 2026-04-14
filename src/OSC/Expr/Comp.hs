{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.Comp where

import Data.Comp
import Data.Comp.Derive

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

gatherAbs :: Term Sig -> Term Sig'
gatherAbs = undefined