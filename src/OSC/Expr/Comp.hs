{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.Comp where

import Data.Comp
import Data.Comp.Ops
import Data.Comp.Derive
import qualified Data.Comp.Multi.Derive as MD

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

    -- Default case: use homomorphism to preserve structure
    gatherAlg :: AlgM (State GatherState) Sig (Term Sig')
    gatherAlg = gatherLam `compAlg` hom
    
    -- Only handle Lam specially, everything else is preserved via homomorphism
    gatherLam :: AlgM (State GatherState) Lam (Term Sig')
    gatherLam (Lam params locals body) = do
      -- Get current function ID and increment
      funcId <- gets nextFuncId
      modify $ \s -> s { nextFuncId = nextFuncId s + 1 }
      
      -- Store the lambda for later (you might want to store it somewhere)
      modify $ \s -> s { collectedFuncs = (funcId, params, locals, body) : collectedFuncs s }
      
      -- Return a function reference
      return $ inject (FuncRef funcId)
    
    -- Homomorphism: inject the functor into the target signature
    hom :: (f :<: Sig') => AlgM (State GatherState) f (Term Sig')
    hom = return . inject

data GatherState = GatherState
  { nextFuncId :: Int
  , collectedFuncs :: [(Int, [String], [(String, Term Sig')], Term Sig')]
  }
