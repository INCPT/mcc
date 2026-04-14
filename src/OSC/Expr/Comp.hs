{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.Comp where

import Data.Comp
import Data.Comp.Derive

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

    -- Algebra that handles Lam specially and preserves everything else
    gatherAlg :: AlgM (State GatherState) Sig (Term Sig')
    gatherAlg = caseF homExp (caseF homValue gatherLam)
    
    -- Preserve Exp via homomorphism
    homExp :: AlgM (State GatherState) Exp (Term Sig')
    homExp = return . inject
    
    -- Preserve Value via homomorphism
    homValue :: AlgM (State GatherState) Value (Term Sig')
    homValue = return . inject
    
    -- Only handle Lam specially
    gatherLam :: AlgM (State GatherState) Lam (Term Sig')
    gatherLam (Lam params locals body) = do
      -- Get current function ID and increment
      funcId <- gets nextFuncId
      modify $ \s -> s { nextFuncId = nextFuncId s + 1 }
      
      -- Store the lambda for later (you might want to store it somewhere)
      modify $ \s -> s { collectedFuncs = (funcId, params, locals, body) : collectedFuncs s }
      
      -- Return a function reference
      return $ inject (FuncRef funcId)

data GatherState = GatherState
  { nextFuncId :: Int
  , collectedFuncs :: [(Int, [String], [(String, Term Sig')], Term Sig')]
  }
