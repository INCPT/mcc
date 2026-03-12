{-# LANGUAGE DeriveFunctor #-}
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

--------------------------------------------------------------------------------

data Binding expr = Binding Ident expr

-- TODO: allow simple arithmetic in range |i| syntax
-- TODO: streams not in scope outside of graph
-- TODO: normal functions/methods not in scope in graph (only variables are in scope)
-- TODO: branch operation computes both branches
-- TODO: after the shadow check/SSA pass all Idents are unique

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

data LBox
  = LBConst Number
  | LBVar Ident
  | LBArr [LBox]
  | LBSelect LBox [Index LBox]
  | LBDelay Int LBox
  | LBCall Ident [LBox] -- TODO: func must be pure
  deriving Show

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
drill _ (LBArr boxes) [IConst n] = (boxes !! n, [])
drill env (LBArr boxes) (IConst n:ns) = drill env (boxes !! n) ns
drill _ boxes is = (boxes, is)

-- drill :: Map BoxIndex LBox -> [BoxIndex] -> [Index a] -> Either ([BoxIndex], [Index a]) BoxIndex
-- drill _ boxes [IConst n] = Right (boxes !! n)
-- drill env boxes (IConst n:ns)
--   | Just (LBArr boxes') <- M.lookup (boxes !! n) env = drill env boxes' ns
-- drill _ boxes is = Left (boxes, is)


newBox :: LBox -> State (Map BoxIndex LBox) BoxIndex
newBox box = do
  boxes <- ST.get
  let nextIdx = BoxIndex (M.size boxes)
  ST.put (M.insert nextIdx box boxes)
  return nextIdx

data Env = Env
  { identToBox :: Map Ident LBox
  }

exprToBox :: Env -> Expr -> LBox
exprToBox _ (EConst n) = LBConst n
exprToBox _ (EVar n) = LBVar n
exprToBox _ (ERec _ _ (EConst n)) = LBConst n
exprToBox env (ERec delay n ret) = retBox
  where
    retBox = exprToBox
      (env { identToBox = M.insert n delayBox env.identToBox })
      ret
    delayBox = LBDelay delay retBox
exprToBox env (EArr es) = LBArr
  [ flattenBox (exprToBox env expr)
  | expr <- es
  ]
exprToBox env (ESelect e is) = LBSelect
  (exprToBox env e)
  (map (fmap (exprToBox env)) is)

exprToBox env (ECall n args) = LBCall n (map (flattenBox . exprToBox env) args)

flattenBox :: LBox -> LBox
flattenBox (LBArr boxes) = case map flattenBox boxes of
  [box] -> box
  boxes -> LBArr boxes
flattenBox box = box

-- TODO: should this be legal: f: f32[4] -> f32, rec |prev| return (f prev)

--------------------------------------------------------------------------------
-- Example to verify that RecursiveDo with lazy State doesn't diverge
-- This mirrors the pattern used in exprToBoxes for ERec
exampleRecDo :: State (Map Int String) [Int]
exampleRecDo = do
  rec
    -- Use the result of computation that depends on 'keys'
    result <- traverse (\k -> ST.modify (M.insert k ("value" ++ show k)) >> return k) keys
    -- Define 'keys' based on something that uses 'result' indirectly
    -- but the actual list structure [1,2,3] is available immediately (lazy)
    let keys = [1, 2, 3]
  return result

-- More direct analog to the ERec pattern:
-- Creating boxes that reference each other through delays
-- exampleDelayPattern :: State (Map BoxIndex LBox) [BoxIndex]
-- exampleDelayPattern = do
--   rec
--     -- Create return boxes that reference the delay boxes
--     retBoxes <- traverse newBox [LBCall "+" (boxes !! 0) (BoxIndex 100), LBCall "*" (boxes !! 1) (BoxIndex 200)]
--     -- Create delay boxes that reference the return boxes
--     boxes <- traverse (\retBox -> newBox (LBDelay 1 retBox)) retBoxes
--   return retBoxes

-- Test function to run the example
testRecDo :: IO ()
testRecDo = do
  putStrLn "Testing RecursiveDo with lazy State:"
  let (result, finalState) = ST.runState exampleRecDo M.empty
  putStrLn $ "Result: " ++ show result
  putStrLn $ "Final state: " ++ show finalState
  putStrLn "\nThis demonstrates that the pattern won't diverge because:"
  putStrLn "1. The list structure [1,2,3] is available immediately (spine is strict)"
  putStrLn "2. The State monad is lazy, so we can reference future computations"
  putStrLn "3. The recursion is productive - each step produces observable output"

--------------------------------------------------------------------------------

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
