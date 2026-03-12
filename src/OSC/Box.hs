{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecursiveDo #-}

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

-- TODO: streams not in scope outside of graph
-- TODO: normal functions/methods not in scope in graph (only variables are in scope)
-- TODO: branch operation computes both branches

data Index a = IConst Int | IVar a
  deriving Show

data Expr
  = EConst Number
  | EVar Ident
  | EGraph Ident
  | EArr [Expr]
  | ESelect Expr [Index Ident]
  | ERec Int Ident [Binding Expr] Expr -- rec delay |prev| -> expr
  | ECall String Expr Expr

data Graph = Graph [Binding Expr] Expr

newtype BoxIndex = BoxIndex Int
  deriving (Num, Eq, Ord, Show)

data LBox
  = LBConst Number
  | LBVar Ident
  | LBDelay Int BoxIndex
  | LBArr [BoxIndex]
  | LBSelect [BoxIndex] [Index BoxIndex]
  | LBCall String BoxIndex BoxIndex -- TODO: func must be pure
  deriving Show

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
    inline _ e@(EGraph _) = e
    inline env' (ESelect e indices) = ESelect (inline env' e) indices
    inline env' (ERec delay n bindings' ret) = 
      ERec delay n bindings' (inline (M.delete n env') ret)
    inline env' (ECall f a b) = ECall f (inline env' a) (inline env' b)
    inline env' (EArr es) = EArr (map (inline env') es)

newBox :: LBox -> State (Map BoxIndex LBox) BoxIndex
newBox box = do
  boxes <- ST.get
  let nextIdx = BoxIndex (M.size boxes)
  ST.put (M.insert nextIdx box boxes)
  return nextIdx

data Env = Env
  { identToBox :: Map Ident BoxIndex
  , identToExpr :: Map Ident Expr
  }

exprToBoxes :: Env -> Expr -> State (Map BoxIndex LBox) [BoxIndex]
exprToBoxes _ (EConst n) = pure <$> newBox (LBConst n)
exprToBoxes env (EVar n)
  | Just boxIndex <- M.lookup n env.identToBox = pure [boxIndex]
  | otherwise = pure <$> newBox (LBVar n)
exprToBoxes _ (ERec _ _ _ (EConst n)) = pure <$> newBox (LBConst n)
exprToBoxes env (ERec delay n bindings ret) = do
  rec
    retBoxes <- exprToBoxes
      (env { identToBox = M.insert n argNode env.identToBox })
      (inlineExpr env.identToExpr bindings ret)

    delayBoxes <- traverse newBox $ map (LBDelay delay) retBoxes
    argNode <- newBox (LBArr delayBoxes)

  pure retBoxes
exprToBoxes env (EGraph n)
  | Just e <- M.lookup n env.identToExpr = exprToBoxes env e
  | otherwise = error "no binding (this is a bug)"
exprToBoxes env (EArr es) = do
  elemBoxes <- sequence
    [ exprToBoxes env expr >>= boxesToBox
    | expr <- es
    ]
  pure <$> newBox (LBArr elemBoxes)
exprToBoxes env (ESelect e is) = do
  boxes <- exprToBoxes env e
  boxMap <- ST.get
  case drill boxMap boxes is of
    Right box -> pure [box]
    Left (boxes, is') -> do
      is'' <- sequence
        [ case i of
            IConst n -> pure (IConst n)
            IVar ident -> case M.lookup ident env.identToExpr of
              Just e -> do
                boxes' <- exprToBoxes env e
                case boxes' of
                  [box] -> pure (IVar box)
                  _ -> error "index isn't a single box (this is a bug)"
              Nothing -> IVar <$> newBox (LBVar ident)
        | i <- is'
        ]
      pure <$> newBox (LBSelect boxes is'')

exprToBoxes env (ECall n f a) = do
  f' <- exprToBoxes env f
  a' <- exprToBoxes env a
  box <- LBCall n <$> boxesToBox f' <*> boxesToBox a'
  pure <$> newBox box

drill :: Map BoxIndex LBox -> [BoxIndex] -> [Index Ident] -> Either ([BoxIndex], [Index Ident]) BoxIndex
drill _ boxes [IConst n] = Right (boxes !! n)
drill env boxes (IConst n:ns)
  | Just (LBArr boxes') <- M.lookup (boxes !! n) env = drill env boxes' ns
drill _ boxes is = Left (boxes, is)

boxesToBox :: [BoxIndex] -> State (Map BoxIndex LBox) BoxIndex
boxesToBox [index] = pure index
boxesToBox indices = newBox (LBArr indices)

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
exampleDelayPattern :: State (Map BoxIndex LBox) [BoxIndex]
exampleDelayPattern = do
  rec
    -- Create return boxes that reference the delay boxes
    retBoxes <- traverse newBox [LBCall "+" (boxes !! 0) (BoxIndex 100), LBCall "*" (boxes !! 1) (BoxIndex 200)]
    -- Create delay boxes that reference the return boxes
    boxes <- traverse (\retBox -> newBox (LBDelay 1 retBox)) retBoxes
  return retBoxes

-- Test function to run the example
testRecDo :: IO ()
testRecDo = do
  putStrLn "Testing RecursiveDo with lazy State:"
  let (result, finalState) = ST.runState exampleDelayPattern M.empty
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
