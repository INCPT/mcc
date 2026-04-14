{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.Comp where

import Data.Comp
import Data.Comp.Ops
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

    gatherAlg :: Alg Sig (State GatherState (Term Sig'))
    gatherAlg (Inl exp) = gatherExp exp
    gatherAlg (Inr (Inl val)) = gatherValue val
    gatherAlg (Inr (Inr lam)) = gatherLam lam

    gatherExp :: Exp (State GatherState (Term Sig')) -> State GatherState (Term Sig')
    gatherExp (Op e1 e2) = do
      e1' <- e1
      e2' <- e2
      return $ iOp e1' e2'
    gatherExp (Var name) = return $ iVar name
    gatherExp (App func args) = do
      func' <- func
      args' <- sequence args
      return $ iApp func' args'
    gatherExp (Select arr idx) = do
      arr' <- arr
      idx' <- idx
      return $ iSelect arr' idx'

    gatherValue :: Value (State GatherState (Term Sig')) -> State GatherState (Term Sig')
    gatherValue (Const n) = return $ iConst n
    gatherValue (Arr elems) = do
      elems' <- sequence elems
      return $ iArr elems'

    gatherLam :: Lam (State GatherState (Term Sig')) -> State GatherState (Term Sig')
    gatherLam (Lam params locals body) = do
      -- Get current function ID and increment
      funcId <- gets nextFuncId
      modify $ \s -> s { nextFuncId = nextFuncId s + 1 }
      
      -- Evaluate the body and locals
      locals' <- mapM (\(name, exp) -> (,) name <$> exp) locals
      body' <- body
      
      -- Store the lambda for later (you might want to store it somewhere)
      modify $ \s -> s { collectedFuncs = (funcId, params, locals', body') : collectedFuncs s }
      
      -- Return a function reference
      return $ inject (FuncRef funcId)

data GatherState = GatherState
  { nextFuncId :: Int
  , collectedFuncs :: [(Int, [String], [(String, Term Sig')], Term Sig')]
  }
