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

--------------------------------------------------------------------------------

data GatherState = GatherState
  { nextFuncId :: Int
  , collectedFuncs :: [(Int, [String], [(String, Term Sig')], Term Sig')]
  }

class GatherAlg f where
  gatherAlg :: AlgM (State GatherState) f (Term Sig')

instance GatherAlg Lam where
  gatherAlg (Lam params locals body) = do
    funcId <- gets nextFuncId
    modify $ \s -> s { nextFuncId = nextFuncId s + 1 }
    modify $ \s -> s { collectedFuncs = (funcId, params, locals, body) : collectedFuncs s }
    return $ inject (FuncRef funcId)

instance {-# OVERLAPPABLE #-} (f :<: Sig') => GatherAlg f where
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

--------------------------------------------------------------------------------
-- Example usage
--------------------------------------------------------------------------------

-- Example: Transform a term with lambda abstractions into one with function references
--
-- Input term (Sig):
--   App (Lam ["x"] [] (Op (Var "x") (Const 1))) [Const 5]
--
-- This represents: (λx. x + 1)(5)
--
-- After gatherAbs, the lambda is extracted and replaced with a FuncRef:
--   App (FuncRef 0) [Const 5]
--
-- The extracted function is stored in the state's collectedFuncs:
--   [(0, ["x"], [], Op (Var "x") (Const 1))]

exampleTerm :: Term Sig
exampleTerm = iApp (iLam ["x"] [] (iOp (iVar "x") (iConst 1))) [iConst 5]

exampleTransformed :: Term Sig'
exampleTransformed = gatherAbs exampleTerm
-- Result: App (FuncRef 0) [Const 5]

-- To get the collected functions:
exampleWithFuncs :: (Term Sig', [(Int, [String], [(String, Term Sig')], Term Sig')])
exampleWithFuncs = runState (cataM gatherAlg exampleTerm) initialState
  where
    initialState = GatherState { nextFuncId = 0, collectedFuncs = [] }
-- Result: (App (FuncRef 0) [Const 5], GatherState { nextFuncId = 1, collectedFuncs = [(0, ["x"], [], Op (Var "x") (Const 1))] })
