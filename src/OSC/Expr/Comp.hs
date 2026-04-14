{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.Comp where

import OSC.Codegen (Type (..), TNumber (..), Stack, push, pop, runStack)
import qualified Control.Monad.State as ST

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

data Select exp = Select exp exp
  deriving Functor

data FoldedSelect exp = FoldedSelectL [exp] exp | FoldedSelectR exp [exp]
  deriving Functor

data Exp exp
  = Op exp exp
  | Var String
  | App exp [exp]
  deriving Functor

data FuncRef exp = FuncRef Int
  deriving Functor

type Sig0 = Exp :+: Value :+: Select       :+: Lam
type Sig1 = Exp :+: Value :+: FoldedSelect :+: Lam
type Sig2 = Exp :+: Value :+: FoldedSelect :+: FuncRef

$(derive
    [ makeTraversable
    , makeFoldable
    , makeEqF
    , makeShowF
    , smartConstructors
    , smartAConstructors
    ]
    [''Value, ''Lam, ''Exp, ''FuncRef, ''Select, ''FoldedSelect]
  )

--------------------------------------------------------------------------------

type FoldSelectionsM = Stack (Type, Term Sig0) (Term Sig1)

foldSelections :: Term Sig0 -> Term Sig1
foldSelections = runStack . expr
  where
    rhs :: Term Sig1 -> FoldSelectionsM
    rhs expr = do
      idxs <- ST.get
      case idxs of
        [] -> pure expr
        _ -> pure $ inject $ FoldedSelectR expr (fmap (foldSelections . snd) idxs)

    expr :: Term Sig0 -> FoldSelectionsM
    expr term = case project term of
      -- Handle Value constructors
      Just (Const n) -> rhs $ inject (Const n)
      Just (Arr es) -> do
        s <- pop
        case s of
          Just (t, idx) -> do
            es' <- traverse expr es
            push (t, idx)
            pure $ inject $ FoldedSelectL es' (foldSelections idx)
          Nothing -> pure $ inject $ Arr (fmap foldSelections es)
      
      -- Handle Exp constructors
      Nothing -> case project term of
        Just (Op a b) -> rhs $ inject $ Op (foldSelections a) (foldSelections b)
        Just (Var n) -> rhs $ inject $ Var n
        Just (App f args) -> rhs $ inject $ App (foldSelections f) (fmap foldSelections args)
        
        -- Handle Lam constructor
        Nothing -> case project term of
          Just (Lam params locals body) -> 
            rhs $ inject $ Lam params (fmap (fmap foldSelections) locals) (foldSelections body)
          
          -- Handle Select constructor
          Nothing -> case project term of
            Just (Select sel idx) -> do
              push (exprType term, idx)
              sel' <- expr sel
              _ <- pop
              pure sel'
            Nothing -> error "foldSelections: unknown constructor"

    exprType :: Term Sig0 -> Type
    exprType term = case project term of
      Just (Const _) -> TNumber TI32  -- Assuming constants are I32
      Just (Arr es) -> case es of
        [] -> error "exprType: empty array"
        (e:_) -> TArr (exprType e) (length es)
      Nothing -> case project term of
        Just (Op _ _) -> TNumber TI32  -- Assuming ops return I32
        Just (Var _) -> error "exprType: cannot determine type of variable"
        Just (App _ _) -> error "exprType: cannot determine type of application"
        Nothing -> case project term of
          Just (Lam _ _ _) -> error "exprType: cannot determine type of lambda"
          Nothing -> case project term of
            Just (Select e _) -> peelType (exprType e)
            Nothing -> error "exprType: unknown constructor"
    
    peelType :: Type -> Type
    peelType (TArr t _) = t
    peelType t = error $ "peelType: cannot peel type " ++ show t

--------------------------------------------------------------------------------

data GatherState = GatherState
  { nextFuncId :: Int
  , collectedFuncs :: [(Int, [String], [(String, Term Sig2)], Term Sig2)]
  } deriving Show

class GatherAlg f where
  gatherAlg :: AlgM (State GatherState) f (Term Sig2)

instance GatherAlg Lam where
  gatherAlg (Lam params locals body) = do
    funcId <- gets nextFuncId
    modify $ \s -> s
      { nextFuncId = nextFuncId s + 1
      , collectedFuncs = (funcId, params, locals, body) : collectedFuncs s
      }
    return $ inject (FuncRef funcId)

instance {-# OVERLAPPABLE #-} (f :<: Sig2) => GatherAlg f where
  gatherAlg = return . inject

instance (GatherAlg f, GatherAlg g) => GatherAlg (f :+: g) where
  gatherAlg (Inl x) = gatherAlg x
  gatherAlg (Inr x) = gatherAlg x

gatherAbs :: Term Sig1 -> Term Sig2
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

exampleTerm :: Term Sig1
exampleTerm = 
  iApp (iLam ["x"] [] 
         (iApp (iLam ["y"] []
                 (iApp (iLam ["z"] []
                        (iOp (iOp (iVar "x") (iVar "y")) (iVar "z")))
                      [iConst 3]))
              [iConst 2]))
       [iConst 1]

exampleTransformed :: Term Sig2
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
exampleWithFuncs :: (Term Sig2, GatherState)
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
