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

    -- Algebra that handles all cases
    gatherAlg :: AlgM (State GatherState) Sig (Term Sig')
    gatherAlg = preserveExp & preserveValue & handleLam
    
    -- Preserve Exp by injecting into Sig'
    preserveExp :: Exp (Term Sig') -> State GatherState (Term Sig')
    preserveExp = return . inject
    
    -- Preserve Value by injecting into Sig'
    preserveValue :: Value (Term Sig') -> State GatherState (Term Sig')
    preserveValue = return . inject
    
    -- Handle Lam specially
    handleLam :: Lam (Term Sig') -> State GatherState (Term Sig')
    handleLam (Lam params locals body) = do
      -- Get current function ID and increment
      funcId <- gets nextFuncId
      modify $ \s -> s { nextFuncId = nextFuncId s + 1 }
      
      -- Store the lambda for later
      modify $ \s -> s { collectedFuncs = (funcId, params, locals, body) : collectedFuncs s }
      
      -- Return a function reference
      return $ inject (FuncRef funcId)

data GatherState = GatherState
  { nextFuncId :: Int
  , collectedFuncs :: [(Int, [String], [(String, Term Sig')], Term Sig')]
  }
