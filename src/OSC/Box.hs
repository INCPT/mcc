{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TupleSections #-}
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

data Index a = IdxConst Int | IdxVar a
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

data BinOp = Plus | Mul | Minus | Div

data Instr
  = ILocalGet LocalIndex
  | ILocalSet LocalIndex
  | ILocalTee LocalIndex  -- set and leave value on stack
  | IConst Number
  | IGlobalGet Ident
  | IGlobalSet Ident
  | ILoad MemAddr  -- i32.load: load from memory at address
  | IStore MemAddr -- i32.store: store to memory at address
  | IBinOp BinOp   -- consumes two stack values, produces one
  | ICall Ident    -- call function, args already on stack
  | IDrop
  
data Program = Program [Instr] (Either LocalSimple LocalArr) -- execute block, return local

type CodegenM = WriterT [Instr] (State (LocalIndex, MemAddr, Map BoxIndex LocalIndex))

reserve :: Int -> CodegenM MemAddr
reserve bytes = do
  (lidx, MemAddr cur, values) <- ST.get
  ST.put (lidx, MemAddr (cur + bytes), values)
  pure (MemAddr cur)

localSimple :: CodegenM LocalIndex
localSimple = do
  (LocalIndex idx, mem, values) <- ST.get
  ST.put (LocalIndex (idx + 1), mem, values)
  pure (LocalIndex idx)

localArray :: Int -> CodegenM (LocalIndex, MemAddr)
localArray size = do
  lidx <- localSimple
  addr <- reserve (size * 4)

  -- Store the base address in the local
  emit $ IConst (I $ let MemAddr a = addr in a)
  emit $ ILocalSet lidx
  pure (lidx, addr)

memoBox :: BoxIndex -> CodegenM LocalIndex -> CodegenM LocalIndex
memoBox box genLocal = do
  (idx, mem, values) <- ST.get
  case M.lookup box values of
    Just local -> pure local
    Nothing -> do
      local <- genLocal
      ST.put (idx, mem, M.insert box local values)
      pure local

emit :: Instr -> CodegenM ()
emit = W.tell . pure

gatherDelays :: Map BoxIndex LBox -> CodegenM (Map BoxIndex LocalIndex)
gatherDelays env = M.fromList <$> sequence
  [ (retBoxIndex,) <$> localSimple
  | LBDelay _ retBoxIndex <- M.elems env
  ]

emitDelays :: Map BoxIndex LocalIndex -> Map BoxIndex LocalIndex -> CodegenM ()
emitDelays localMap delayMap = sequence_
  [ do
      emit $ ILocalGet retLocal
      emit $ ILocalSet delayLocal
  | (retBoxIndex, delayLocal) <- M.toList delayMap
  , Just retLocal <- [ M.lookup retBoxIndex localMap ]
  ]

boxToBlock :: Map BoxIndex LBox -> Map BoxIndex LocalIndex -> LBox -> CodegenM LocalIndex
boxToBlock _ _ (LBConst n) = do
  lidx <- localSimple
  emit $ IConst n
  emit $ ILocalSet lidx
  pure lidx
boxToBlock _ _ (LBVar n) = do
  lidx <- localSimple
  emit $ IGlobalGet n
  emit $ ILocalSet lidx
  pure lidx
boxToBlock env delayMap (LBArr dims boxes) = do
  (lidx, MemAddr baseAddr) <- localArray (product dims)
  sequence_
    [ do
        valueLocal <- boxToBlockMemo env delayMap boxIndex box
        emit $ ILocalGet valueLocal
        emit $ IStore (MemAddr $ baseAddr + index * 4)
    | (index, boxIndex) <- zip [0..] boxes
    , Just box <- [ M.lookup boxIndex env ]
    ]
  pure lidx
boxToBlock env delayMap (LBSelect dims boxIndex indices)
  | Just box <- M.lookup boxIndex env = do
      baseLocal <- boxToBlockMemo env delayMap boxIndex box
      offsetLocal <- localSimple
      emit $ IConst (I 0)
      emit $ ILocalSet offsetLocal
      
      -- Calculate offset: sum of (index * cardinality) for each dimension
      sequence_
        [ case idx of
            IdxConst i -> do
              emit $ ILocalGet offsetLocal
              emit $ IConst (I (i * card))
              emit $ IBinOp Plus
              emit $ ILocalSet offsetLocal
            IdxVar indexBoxIndex
              | Just indexBox <- M.lookup indexBoxIndex env -> do
                  idxLocal <- boxToBlockMemo env delayMap indexBoxIndex indexBox
                  emit $ ILocalGet offsetLocal
                  emit $ ILocalGet idxLocal
                  emit $ IConst (I card)
                  emit $ IBinOp Mul
                  emit $ IBinOp Plus
                  emit $ ILocalSet offsetLocal
              | otherwise -> error "select: index (this is a bug)"
        | (card, idx) <- zip (scanl (*) 1 dims) indices
        ]
      
      -- Load from base + offset
      res <- localSimple
      emit $ ILocalGet baseLocal
      emit $ ILocalGet offsetLocal
      emit $ IConst (I 4)  -- 4 bytes per element
      emit $ IBinOp Mul
      emit $ IBinOp Plus
      emit $ ILoad (MemAddr 0)  -- offset is already in the address
      emit $ ILocalSet res
      pure res
  | otherwise = error "select: box (this is a bug)"
boxToBlock _ delayMap (LBDelay _ retBoxIndex)
  | Just delayLocal <- M.lookup retBoxIndex delayMap = pure delayLocal
  | otherwise = error "delay (this is a bug)"
boxToBlock env delayMap (LBCall n argBoxIndices) = do
  -- Push all arguments onto the stack
  sequence_
    [ case M.lookup argBoxIndex env of
        Just box -> do
          argLocal <- boxToBlockMemo env delayMap argBoxIndex box
          emit $ ILocalGet argLocal
        Nothing -> error "call: arg box not found (this is a bug)"
    | argBoxIndex <- argBoxIndices
    ]
  
  -- Call function (args are on stack)
  emit $ ICall n
  
  -- Store result
  res <- localSimple
  emit $ ILocalSet res
  pure res

boxToBlockMemo :: Map BoxIndex LBox -> Map BoxIndex LocalIndex -> BoxIndex -> LBox -> CodegenM LocalIndex
boxToBlockMemo env delayMap k lbox = memoBox k (boxToBlock env delayMap lbox)
