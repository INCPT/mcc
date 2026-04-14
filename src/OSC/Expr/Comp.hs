{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.Comp where

import Data.Function ((&))
import Data.Comp
import Data.Comp.Derive
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

gatherAbs :: Term Sig -> Term Sig'
gatherAbs term = evalState (cataM gatherAlg term) initialState
  where
    initialState :: GatherState
    initialState = GatherState
      { nextFuncId = 0
      , collectedFuncs = []
      }

    -- Algebra that handles all cases - order independent
    gatherAlg :: Sig (Term Sig') -> State GatherState (Term Sig')
    gatherAlg sig = case proj sig of
      Just (Lam params locals body) -> do
        funcId <- gets nextFuncId
        modify $ \s -> s { nextFuncId = nextFuncId s + 1 }
        modify $ \s -> s { collectedFuncs = (funcId, params, locals, body) : collectedFuncs s }
        return $ inject (FuncRef funcId)
      Nothing -> return $ inject sig

data GatherState = GatherState
  { nextFuncId :: Int
  , collectedFuncs :: [(Int, [String], [(String, Term Sig')], Term Sig')]
  }
