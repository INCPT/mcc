{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecursiveDo #-}
{-# OPTIONS_GHC -fno-defer-type-errors #-}

module OSC.Box where

import qualified Control.Monad.State as ST
import Control.Monad.State.Lazy (State)

import qualified Data.Map as M
import Data.Map (Map)

data Number = I Int | F Double
  deriving Show

data Ident = Ident String
  deriving (Eq, Ord, Show)

data Box
  = BConst Number
  | BVar Ident
  | BDelay Ident Int Box
  | BFunc String Box Box -- TODO: func must be pure

flow :: Box -> String
flow (BConst n) = show n
flow (BVar (Ident v)) = v
flow (BFunc f a b) = "((" <> flow a <> ") " <> f <> " (" <> flow b <> "))"
flow (BDelay (Ident n) _ _) = n

gatherDelays :: Box -> [(Ident, Box)]
gatherDelays (BDelay n _ b) = [(n, b)]
gatherDelays (BFunc _ a b) = gatherDelays a <> gatherDelays b
gatherDelays _ = []

codegen :: Box -> IO ()
codegen b = do
  putStrLn $ "out = " <> flow b
  sequence_
    [ putStrLn $ n <> " = " <> flow b'
    | (Ident n, b') <- gatherDelays b
    ]

b1 :: Box
b1 = BFunc "+" (BConst (I 5)) (BVar (Ident "sample_rate"))

b2 :: Box
b2 = res
  where
    prev = BDelay (Ident "prev" ) 1 res
    res = BFunc "+" prev (BConst (I 1))

-- desugar :: Map Ident Expr -> Graph -> State BoxIndex [LBox]
-- desugar env (Graph bindings ret) = sequence
--   [ undefined
--   | Binding n e <- bindings
--   ]
--   where
--     -- TODO no shadowing etc
--     innerEnv =  M.fromList
--       [ (n, e)
--       | Binding n e <- bindings
--       ]

--------------------------------------------------------------------------------

data Binding expr = Binding Ident expr

-- TODO: allow simple arithmetic in range |i| syntax
-- TODO: streams not in scope outside of graph
-- TODO: normal functions/methods not in scope in graph (only variables are in scope)
-- TODO: branch operation computes both branches
-- TODO: after the shadow check/SSA pass all Idents are unique

-- TODO: should this be legal: f: f32[4] -> f32, rec |prev| return (f prev)

data Index a = IConst Int | IVar a
  deriving (Show, Functor)

data Expr'
  = EConst' Number
  | EVar' Ident
  | EGraphCall' Ident [Expr]
  | ECall' Ident [Expr]
  | EArr' [Expr']
  | ESelect' Expr [Index Ident]
  | ERec' Int Ident [Binding Expr'] Expr' -- rec delay |prev| -> expr

-- the above gets expanded to:
-- TODO: in ESelect the Expr is maximally drilled into
--     Right box -> pure [box]
--     Left (boxes, is') -> do
--       is'' <- sequence
--         [ case i of
--             IConst n -> pure (IConst n)
--             IVar expr -> do
--               boxes' <- exprToBoxes env expr
--               case boxes' of
--                 [box] -> pure (IVar box)
--                 _ -> error "index isn't a single box (this is a bug)"
--         | i <- is'
--         ]
--       pure <$> newBox (LBSelect boxes is'')
--   where
--     box = exprToBox env e

data Expr
  = EConst Number
  | EVar Ident
  | EArr [Expr]
  | ESelect Expr [Index Expr]
  | ERec Int Ident Expr -- rec delay |prev| -> expr
  | ECall Ident [Expr]

data Graph = Graph [Binding Expr] Expr

newtype BoxIndex = BoxIndex Int
  deriving (Num, Eq, Ord, Show)

{-
inlineExpr :: Map Ident Expr -> [Binding Expr] -> Expr -> Expr
inlineExpr env bindings expr = inline (env `M.union` bindingMap) expr
  where
    -- TODO: semantic check of no mutual or self recursion between exprs/boxes
    -- TODO: no shadowing etc
    bindingMap = M.fromList [(n, e) | Binding n e <- bindings]
    
    inline :: Map Ident Expr -> Expr -> Expr
    inline env' (EVar n)
      | Just e <- M.lookup n env' = inline env' e
      | otherwise = EVar n
    inline _ e@(EConst _) = e
    inline env' (ESelect e indices) = ESelect (inline env' e) indices
    inline env' (ERec delay n bindings' ret) = 
      ERec delay n bindings' (inline (M.delete n env') ret)
    inline env' (ECall f args) = ECall f (fmap (inline env') args)
    inline env' (EArr es) = EArr (map (inline env') es)
-}

drill :: Map Ident LBox -> LBox -> [Index a] -> (LBox, [Index a])
drill _ (Fix (LBArrF boxes)) [IConst n] = (boxes !! n, [])
drill env (Fix (LBArrF boxes)) (IConst n:ns) = drill env (boxes !! n) ns
drill _ boxes is = (boxes, is)

-- drill :: Map BoxIndex LBox -> [BoxIndex] -> [Index a] -> Either ([BoxIndex], [Index a]) BoxIndex
-- drill _ boxes [IConst n] = Right (boxes !! n)
-- drill env boxes (IConst n:ns)
--   | Just (LBArr boxes') <- M.lookup (boxes !! n) env = drill env boxes' ns
-- drill _ boxes is = Left (boxes, is)

flattenBox :: LBox -> LBox
flattenBox (Fix (LBArrF boxes)) = case map flattenBox boxes of
  [box] -> box
  boxes' -> Fix (LBArrF boxes')
flattenBox box = box



newBox :: LBox -> State (Map BoxIndex LBox) BoxIndex
newBox box = do
  boxes <- ST.get
  let nextIdx = BoxIndex (M.size boxes)
  ST.put (M.insert nextIdx box boxes)
  return nextIdx

--------------------------------------------------------------------------------

newtype Fix f = Fix { unFix :: f (Fix f) }

data LBoxF r
  = LBConstF Number
  | LBVarF Ident
  | LBArrF [r]
  | LBSelectF r [Index r] -- maximally drilled into
  | LBDelayF Int r
  | LBCallF Ident [r]
  deriving (Show, Functor)

type LBox = Fix LBoxF

instance Show (Fix LBoxF) where
  show (Fix f) = show f

data Env = Env
  { identToBox :: Map Ident LBox
  }

exprToBox :: Env -> Expr -> LBox
exprToBox _ (EConst n) = Fix (LBConstF n)
exprToBox _ (EVar n) = Fix (LBVarF n)
exprToBox _ (ERec _ _ (EConst n)) = Fix (LBConstF n)
exprToBox env (ERec delay n ret) = retBox
  where
    retBox = exprToBox
      (env { identToBox = M.insert n delayBox env.identToBox })
      ret
    delayBox = Fix (LBDelayF delay retBox)
exprToBox env (EArr es) = Fix (LBArrF (map (exprToBox env) es))
exprToBox env (ESelect e is) = Fix (LBSelectF
  (exprToBox env e)
  (map (fmap (exprToBox env)) is))
exprToBox env (ECall n args) = Fix (LBCallF n (map (exprToBox env) args))

--------------------------------------------------------------------------------

-- TODO: after component clustering, if a component is called only once, inline

data Addr

data Local = Simple Addr | Array Addr Int

data Block
  = Local (Local -> Block)
  | Load Local Ident
  | Write Local Block -- local, value
  | WriteArr Local Block Block -- local, index, value
  | Call Ident [Local]
  
data Program = Program [Block] Local -- execute block, return local
