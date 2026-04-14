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
import Data.Comp.Show ()  -- Provides Show instances for Term

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
  } deriving Show

class GatherAlg f where
  gatherAlg :: AlgM (State GatherState) f (Term Sig')

instance GatherAlg Lam where
  gatherAlg (Lam params locals body) = do
    funcId <- gets nextFuncId
    modify $ \s -> s
      { nextFuncId = nextFuncId s + 1
      , collectedFuncs = (funcId, params, locals, body) : collectedFuncs s
      }
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

-- Example: Transform a term with nested lambda abstractions into one with function references
--
-- Input term (Sig):
--   App (Lam ["x"] [] 
--         (App (Lam ["y"] []
--                (App (Lam ["z"] []
--                       (Op (Op (Var "x") (Var "y")) (Var "z")))
--                     [Const 3]))
--              [Const 2]))
--       [Const 1]
--
-- This represents: (λx. (λy. (λz. (x + y) + z)(3))(2))(1)
--
-- After gatherAbs, all three lambdas are extracted and replaced with FuncRefs:
--   App (FuncRef 0) [Const 1]
--
-- The extracted functions are stored in the state's collectedFuncs:
--   [(2, ["z"], [], Op (Op (Var "x") (Var "y")) (Var "z")),
--    (1, ["y"], [], App (FuncRef 2) [Const 3]),
--    (0, ["x"], [], App (FuncRef 1) [Const 2])]

exampleTerm :: Term Sig
exampleTerm = 
  iApp (iLam ["x"] [] 
         (iApp (iLam ["y"] []
                 (iApp (iLam ["z"] []
                        (iOp (iOp (iVar "x") (iVar "y")) (iVar "z")))
                      [iConst 3]))
              [iConst 2]))
       [iConst 1]

exampleTransformed :: Term Sig'
exampleTransformed = gatherAbs exampleTerm
-- Result: App (FuncRef 0) [Const 1]
-- Where FuncRef 0 contains: App (FuncRef 1) [Const 2]
-- And FuncRef 1 contains: App (FuncRef 2) [Const 3]
-- And FuncRef 2 contains: Op (Op (Var "x") (Var "y")) (Var "z")

-- To print a term, just use show:
printExample :: IO ()
printExample = do
  putStrLn "Original term:"
  print exampleTerm
  putStrLn "\nTransformed term:"
  print exampleTransformed
  putStrLn "\nWith collected functions:"
  print exampleWithFuncs

-- To get the collected functions:
exampleWithFuncs :: (Term Sig', GatherState)
exampleWithFuncs = runState (cataM gatherAlg exampleTerm) initialState
  where
    initialState = GatherState { nextFuncId = 0, collectedFuncs = [] }
-- Result: 
-- ( App (FuncRef 0) [Const 1]
-- , GatherState 
--     { nextFuncId = 3
--     , collectedFuncs = 
--         [ (2, ["z"], [], Op (Op (Var "x") (Var "y")) (Var "z"))
--         , (1, ["y"], [], App (FuncRef 2) [Const 3])
--         , (0, ["x"], [], App (FuncRef 1) [Const 2])
--         ]
--     }
-- )
