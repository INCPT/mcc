{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecursiveDo #-}
{-# OPTIONS_GHC -fno-defer-type-errors #-}

module OSC.Box where

import qualified Control.Monad.State as ST
import Control.Monad.State.Lazy (State)
import qualified Control.Monad.Writer.CPS as W
import Control.Monad.Writer.CPS (WriterT)

import qualified Data.Map as M
import Data.Map (Map)

data Number = I Int | F Double
  deriving Show

data Ident = Ident String
  deriving (Eq, Ord, Show)

-- data Box
--   = BConst Number
--   | BVar Ident
--   | BDelay Ident Int Box
--   | BFunc String Box Box -- TODO: func must be pure
-- 
-- flow :: Box -> String
-- flow (BConst n) = show n
-- flow (BVar (Ident v)) = v
-- flow (BFunc f a b) = "((" <> flow a <> ") " <> f <> " (" <> flow b <> "))"
-- flow (BDelay (Ident n) _ _) = n
-- 
-- gatherDelays :: Box -> [(Ident, Box)]
-- gatherDelays (BDelay n _ b) = [(n, b)]
-- gatherDelays (BFunc _ a b) = gatherDelays a <> gatherDelays b
-- gatherDelays _ = []
-- 
-- codegen :: Box -> IO ()
-- codegen b = do
--   putStrLn $ "out = " <> flow b
--   sequence_
--     [ putStrLn $ n <> " = " <> flow b'
--     | (Ident n, b') <- gatherDelays b
--     ]
-- 
-- b1 :: Box
-- b1 = BFunc "+" (BConst (I 5)) (BVar (Ident "sample_rate"))
-- 
-- b2 :: Box
-- b2 = res
--   where
--     prev = BDelay (Ident "prev" ) 1 res
--     res = BFunc "+" prev (BConst (I 1))

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
  deriving (Show, Functor, Foldable, Traversable)

data Expr'
  = EConst' Number
  | EVar' Ident
  | EGraphCall' Ident [Expr]
  | ECall' Ident [Expr]
  | EArr' [Expr']
  | ESelect' Expr [Index Ident]
  | ERec' Int Ident [Binding Expr'] Expr' -- rec delay |prev| -> expr

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

-- TODO: expand as much as possible and maximally drill into Exprs
-- TODO: idents in CallGraphs should be preserved so we can utilize the sharing when performing the shared component analysis
expandExpr :: Expr' -> Expr
expandExpr = undefined

data Type = TSimple | TArray Int
  deriving Show

data Expr
  = EConst Number
  | EVar Ident
  | EArr [Int] [Expr] -- dims
  | ESelect [Int] Expr [Index Expr] -- dims
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

-- drill :: Map BoxIndex LBox -> BoxIndex -> [Index a] -> (BoxIndex, [Index a])
-- drill boxMap lbl [IConst n]
--   | Just (LBArr labels) <- M.lookup lbl boxMap = (labels !! n, [])
-- drill boxMap lbl (IConst n:ns)
--   | Just (LBArr labels) <- M.lookup lbl boxMap = drill boxMap (labels !! n) ns
-- drill _ lbl is = (lbl, is)

-- drill :: Map BoxIndex LBox -> [BoxIndex] -> [Index a] -> Either ([BoxIndex], [Index a]) BoxIndex
-- drill _ boxes [IConst n] = Right (boxes !! n)
-- drill env boxes (IConst n:ns)
--   | Just (LBArr boxes') <- M.lookup (boxes !! n) env = drill env boxes' ns
-- drill _ boxes is = Left (boxes, is)

-- flattenBox :: Map BoxIndex LBox -> BoxIndex -> (BoxIndex, Map BoxIndex LBox)
-- flattenBox boxMap lbl
--   | Just (LBArr _ labels) <- M.lookup lbl boxMap =
--       case labels of
--         [singleBoxIndex] -> (singleBoxIndex, boxMap)
--         _ -> (lbl, boxMap)
--   | otherwise = (lbl, boxMap)

--------------------------------------------------------------------------------

type BoxGenM = State (BoxIndex, Map BoxIndex LBox)

newBox :: LBox -> BoxGenM BoxIndex
newBox box = do
  (nextBoxIndex, boxes) <- ST.get
  ST.put (nextBoxIndex + 1, M.insert nextBoxIndex box boxes)
  return nextBoxIndex

data LBox
  = LBConst Number
  | LBVar Ident
  | LBArr [Int] [BoxIndex] -- dimensions
  | LBSelect [Int] BoxIndex [Index BoxIndex] -- maximally drilled into
  | LBDelay Int BoxIndex
  | LBCall Ident [BoxIndex]
  deriving Show

exprToBox :: Map Ident BoxIndex -> Expr -> BoxGenM BoxIndex
exprToBox _ (EConst n) = newBox (LBConst n)
exprToBox _ (EVar n) = newBox (LBVar n)
exprToBox _ (ERec _ _ (EConst n)) = newBox (LBConst n)
exprToBox env (ERec delay n ret) = mdo
  retBoxIndex <- exprToBox (M.insert n delayBoxIndex env) ret
  delayBoxIndex <- newBox (LBDelay delay retBoxIndex)
  pure retBoxIndex
exprToBox env (EArr dims es) = do
  labels <- traverse (exprToBox env) es
  newBox (LBArr dims labels)
exprToBox env (ESelect dims e is) = do
  eBoxIndex <- exprToBox env e
  isBoxIndexs <- traverse (traverse (exprToBox env)) is
  newBox (LBSelect dims eBoxIndex isBoxIndexs)
exprToBox env (ECall n args) = do
  argBoxIndexs <- traverse (exprToBox env) args
  newBox (LBCall n argBoxIndexs)

--------------------------------------------------------------------------------

-- TODO: after component clustering, if a component is called only once, inline

newtype LocalIndex = LocalIndex Int
  deriving Num

newtype MemAddr = MemAddr Int
  deriving Num

data LocalSimple = LSimple LocalIndex
data LocalArr = LArr LocalIndex MemAddr Int

data BinOp = Plus | Mul

data Instr
  = ILoadAddr LocalIndex Ident
  | ILoadAddr'' LocalIndex MemAddr
  | ILoadOffset LocalIndex LocalIndex Value -- local <- base[value]
  | ILoadVal LocalIndex LocalIndex
  | IStore MemAddr Value -- local, index, value
  | ICall Ident [LocalSimple]
  | IBinOp BinOp LocalIndex Value
  
data Program = Program [Instr] (Either LocalSimple LocalArr) -- execute block, return local

type CodegenM = WriterT [Instr] (State (LocalIndex, MemAddr, Map BoxIndex Value))

reserve :: Int -> CodegenM MemAddr
reserve bytes = do
  (lidx, MemAddr cur, values) <- ST.get
  ST.put (lidx, MemAddr (cur + bytes), values)
  pure (MemAddr (cur + bytes))

localSimple :: CodegenM LocalIndex
localSimple = do
  (LocalIndex idx, mem, values) <- ST.get
  ST.put (LocalIndex (idx + 4), mem, values)
  pure (LocalIndex idx)

localArray :: Int -> CodegenM (LocalIndex, MemAddr)
localArray size = do
  (LocalIndex idx, MemAddr cur, values) <- ST.get
  ST.put (LocalIndex (idx + 4), MemAddr (cur + size * 4), values)
  emit $ ILoadAddr'' (LocalIndex idx) (MemAddr cur)
  pure (LocalIndex idx, MemAddr cur)

cache :: BoxIndex -> CodegenM Value -> CodegenM Value
cache box genValue = do
  (idx, mem, values) <- ST.get
  case M.lookup box values of
    Just value' -> pure value'
    Nothing -> do
      value <- genValue
      ST.put (idx, mem, M.insert box value values)
      pure value

emit :: Instr -> CodegenM ()
emit = W.tell . pure

data Value = VConst Number | VLocal LocalIndex

boxToBlock :: Map BoxIndex LBox -> LBox -> CodegenM Value
boxToBlock _ (LBConst n) = pure (VConst n)
boxToBlock _ (LBVar n) = do
  lidx <- localSimple
  emit $ ILoadAddr lidx n
  pure $ VLocal lidx
boxToBlock env (LBArr dims boxes) = do
  (lidx, MemAddr mem) <- localArray (product dims)
  sequence_
    [ do
        value <- cache boxIndex (boxToBlock env box)
        emit $ IStore (MemAddr $ mem + index * 4) value
    | (index, boxIndex) <- zip [0..] boxes
    , Just box <- [ M.lookup boxIndex env ]
    ]
  pure $ VLocal lidx
boxToBlock env (LBSelect dims boxIndex indices)
  | Just box <- M.lookup boxIndex env = do
      bsel <- cache boxIndex (boxToBlock env box)
      case bsel of
        VConst _ -> error "select: bsel (this is a bug)"
        VLocal bsel' -> do
          lidx <- localSimple
          res <- localSimple
          sequence_
            [ case idx of
                IConst i -> emit $ IBinOp Plus lidx (VConst $ I (i * card))
                IVar indexBoxIndex
                  | Just indexBox <- M.lookup indexBoxIndex env -> do
                      vidx <- cache indexBoxIndex (boxToBlock env indexBox)
                      case vidx of
                        VConst (I i) -> emit $ IBinOp Plus lidx (VConst $ I (i * card))
                        VConst _ -> error "select: index not natural (this is a bug)"
                        VLocal i -> do
                          emit $ IBinOp Mul i (VConst $ I card)
                          emit $ IBinOp Plus lidx (VLocal i)
                  | otherwise -> error "select: index (this is a bug)"
            | (card, idx) <- zip (scanl (*) 1 dims) indices
            ]
          emit $ ILoadOffset res bsel' (VLocal lidx)
          pure $ VLocal res
  | otherwise = error "select: box (this is a bug)"
boxToBlock env (LBDelay delay box) = undefined
boxToBlock env (LBCall n args) = undefined
