{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-defer-type-errors #-}

module OSC.Box where

import Control.Monad (when)
import qualified Control.Monad.State as ST
import Control.Monad.State.Lazy (State, StateT)
import qualified Control.Monad.Writer.CPS as W
import Control.Monad.Writer.CPS (Writer)

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
  deriving Show

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

inlineRef :: Ident -> Expr -> Expr -> Expr
inlineRef n replace expr = inline expr
  where
    inline (EVar v)
      | v == n = replace
      | otherwise = EVar v
    inline e@(EConst _) = e
    inline (EArr dims es) = EArr dims (map inline es)
    inline (ESelect dims e is) = ESelect dims (inline e) (map (fmap inline) is)
    inline (ERec delay v ret)
      | v == n = ERec delay v ret  -- shadowed, don't recurse
      | otherwise = ERec delay v (inline ret)
    inline (ECall f args) = ECall f (map inline args)

mergeSelects :: Expr -> Expr
mergeSelects (ESelect outerDims e outerIndices) =
  case mergeSelects e of
    -- If selecting from another select, combine them
    ESelect innerDims innerExpr innerIndices ->
      ESelect innerDims (mergeSelects innerExpr) (outerIndices <> innerIndices)
    -- Otherwise, recurse on the expression being selected from
    e' -> ESelect outerDims e' (map (fmap mergeSelects) outerIndices)
mergeSelects (EArr dims es) = EArr dims (map mergeSelects es)
mergeSelects (ERec delay n ret) = ERec delay n (mergeSelects ret)
mergeSelects (ECall f args) = ECall f (map mergeSelects args)
mergeSelects e@(EConst _) = e
mergeSelects e@(EVar _) = e

exprToBox :: Map Ident BoxIndex -> Expr -> BoxGenM BoxIndex
exprToBox _ (EConst n) = newBox (LBConst n)
exprToBox env (EVar n)
  | Just boxIndex <- M.lookup n env = pure boxIndex
  | otherwise = newBox (LBVar n)
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
  deriving (Num, Eq, Ord, Show)

newtype MemAddr = MemAddr Int
  deriving (Num, Eq, Ord, Show)

data LocalSimple = LSimple LocalIndex deriving (Eq, Ord, Show)
data LocalArr = LArr LocalIndex MemAddr Int deriving (Eq, Ord, Show)

data BinOp = Plus | Mul | Minus | Div deriving Show

data Instr
  = ILocalGet LocalIndex
  | ILocalSet LocalIndex
  | ILocalTee LocalIndex  -- set and leave value on stack
  | IConst Number
  | IGlobalGet Ident
  | IGlobalSet Ident
  | ILoad MemAddr  -- i32.load offset: load from (stack_addr + offset)
  | IStore MemAddr -- i32.store offset: store to (stack_addr + offset)
  | IBinOp BinOp   -- consumes two stack values, produces one
  | ICall Ident    -- call function, args already on stack
  deriving Show

data MState = MState
  { locals :: Map LocalIndex Number
  , stack :: [Number]
  , memory :: Map MemAddr Number
  , globals :: Map Ident Number
  }
  deriving Show

emptyMState :: MState
emptyMState = MState
  { locals = mempty
  , stack = []
  , memory = mempty
  , globals = mempty
  }

interpet :: (LocalIndex, [LocalIndex], [Instr]) -> (Maybe Number, MState)
interpet (retIndex, locals, instrs) = (M.lookup retIndex state.locals, state)
  where
    state = go (emptyMState { locals = M.fromList (fmap (, I 0) locals) }) instrs

    go :: MState -> [Instr] -> MState
    go res [] = res
    go res (instr:rest) = case instr of
      ILocalGet idx ->
        case M.lookup idx res.locals of
          Just val -> go (res { stack = val : res.stack }) rest
          Nothing -> error $ "Local not found: " ++ show idx
      
      ILocalSet idx ->
        case res.stack of
          (val:stackRest) ->
            go (res { locals = M.insert idx val res.locals, stack = stackRest }) rest
          [] -> error "Stack underflow on ILocalSet"
      
      ILocalTee idx ->
        case res.stack of
          (val:_) ->
            go (res { locals = M.insert idx val res.locals }) rest
          [] -> error "Stack underflow on ILocalTee"
      
      IConst n ->
        go (res { stack = n : res.stack }) rest
      
      IGlobalGet ident ->
        case M.lookup ident res.globals of
          Just val -> go (res { stack = val : res.stack }) rest
          Nothing -> error $ "Global not found: " ++ show ident
      
      IGlobalSet ident ->
        case res.stack of
          (val:stackRest) ->
            go (res { globals = M.insert ident val res.globals, stack = stackRest }) rest
          [] -> error "Stack underflow on IGlobalSet"
      
      ILoad (MemAddr offset) ->
        case res.stack of
          (I baseAddr:stackRest) ->
            let addr = MemAddr (baseAddr + offset)
            in case M.lookup addr res.memory of
              Just val -> go (res { stack = val : stackRest }) rest
              Nothing -> go (res { stack = I 0 : stackRest }) rest  -- uninitialized memory reads as 0
          _ -> error "Stack underflow or type error on ILoad"
      
      IStore (MemAddr offset) ->
        case res.stack of
          (val:I baseAddr:stackRest) ->
            let addr = MemAddr (baseAddr + offset)
            in go (res { memory = M.insert addr val res.memory, stack = stackRest }) rest
          _ -> error "Stack underflow or type error on IStore"
      
      IBinOp op ->
        case res.stack of
          (b:a:stackRest) ->
            let result = evalBinOp op a b
            in go (res { stack = result : stackRest }) rest
          _ -> error "Stack underflow on IBinOp"
      
      ICall _ident ->
        -- For now, just pop arguments and push a dummy result
        -- In a real implementation, this would look up and execute the function
        go res rest

evalBinOp :: BinOp -> Number -> Number -> Number
evalBinOp Plus (I a) (I b) = I (a + b)
evalBinOp Plus (F a) (F b) = F (a + b)
evalBinOp Plus (I a) (F b) = F (fromIntegral a + b)
evalBinOp Plus (F a) (I b) = F (a + fromIntegral b)
evalBinOp Minus (I a) (I b) = I (a - b)
evalBinOp Minus (F a) (F b) = F (a - b)
evalBinOp Minus (I a) (F b) = F (fromIntegral a - b)
evalBinOp Minus (F a) (I b) = F (a - fromIntegral b)
evalBinOp Mul (I a) (I b) = I (a * b)
evalBinOp Mul (F a) (F b) = F (a * b)
evalBinOp Mul (I a) (F b) = F (fromIntegral a * b)
evalBinOp Mul (F a) (I b) = F (a * fromIntegral b)
evalBinOp Div (I a) (I b) = I (a `div` b)
evalBinOp Div (F a) (F b) = F (a / b)
evalBinOp Div (I a) (F b) = F (fromIntegral a / b)
evalBinOp Div (F a) (I b) = F (a / fromIntegral b)

--------------------------------------------------------------------------------

data CodegenEnv = CodegenEnv
  { nextLocal :: LocalIndex
  , nextMem :: MemAddr
  , values :: Map BoxIndex LocalIndex
  , locals :: [LocalIndex]
  }
  
type CodegenM = StateT CodegenEnv (Writer [Instr])

reserve :: Int -> CodegenM MemAddr
reserve bytes = do
  env <- ST.get
  let MemAddr cur = env.nextMem
  ST.put $ env { nextMem = MemAddr (cur + bytes) }
  pure (MemAddr cur)

localSimple :: CodegenM LocalIndex
localSimple = do
  env <- ST.get
  let (LocalIndex idx) = env.nextLocal
  ST.put $ env { nextLocal = LocalIndex (idx + 1), locals = env.locals ++ [env.nextLocal] }
  pure env.nextLocal

localArray :: Int -> CodegenM (LocalIndex, MemAddr)
localArray size = do
  lidx <- localSimple
  addr <- reserve (size * 4)

  -- Store the base address in the local
  emit $ IConst (I $ let MemAddr a = addr in a)
  emit $ ILocalSet lidx
  pure (lidx, addr)

memoBox :: BoxIndex -> CodegenM LocalIndex -> CodegenM LocalIndex
memoBox boxIndex genLocal = do
  env <- ST.get
  case M.lookup boxIndex env.values of
    Just local -> pure local
    Nothing -> mdo
      -- This works because the state is lazy; we update the state first here because
      -- genLocal is recursive and won't return and thus the state will be updated
      -- only at the end
      ST.put $ env { values = M.insert boxIndex local env.values }
      local <- genLocal
      pure local

emit :: Instr -> CodegenM ()
emit = W.tell . pure

gatherDelays :: Map BoxIndex LBox -> CodegenM (Map BoxIndex LocalIndex)
gatherDelays env = M.fromList <$> sequence
  [ (retBoxIndex,) <$> localSimple
  | LBDelay _ retBoxIndex <- M.elems env
  ]

emitDelays :: Map BoxIndex LocalIndex -> CodegenM ()
emitDelays delayMap = do
  env <- ST.get
  sequence_
    [ do
        emit $ ILocalGet retLocal
        emit $ ILocalSet delayLocal
    | (retBoxIndex, delayLocal) <- M.toList delayMap
    , Just retLocal <- [ M.lookup retBoxIndex env.values ]
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
  (lidx, _) <- localArray (product dims)
  sequence_
    [ do
        -- For constants, emit directly without creating a local
        case box of
          LBConst n -> do
            emit $ ILocalGet lidx  -- base address on stack
            emit $ IConst n  -- value on stack
            emit $ IStore (MemAddr (index * 4))  -- store to (stack_addr + offset)
          _ -> do
            valueLocal <- boxToBlockMemo env delayMap boxIndex box
            emit $ ILocalGet lidx  -- base address on stack
            emit $ ILocalGet valueLocal  -- value on stack
            emit $ IStore (MemAddr (index * 4))  -- store to (stack_addr + offset)
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
            IdxConst 0 -> pure ()
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
                  when (card > 1) $ do
                    emit $ IConst (I card)
                    emit $ IBinOp Mul
                  emit $ IBinOp Plus
                  emit $ ILocalSet offsetLocal
              | otherwise -> error "select: index (this is a bug)"
        | (card, idx) <- zip (scanl (*) 1 dims) indices
        ]
      
      -- Load from base + offset
      res <- localSimple

      -- Push base address + (offset * 4) onto stack, then load
      emit $ ILocalGet baseLocal
      emit $ ILocalGet offsetLocal
      emit $ IConst (I 4)  -- 4 bytes per element
      emit $ IBinOp Mul
      emit $ IBinOp Plus
      emit $ ILoad (MemAddr 0)  -- load from (stack_addr + 0)
      emit $ ILocalSet res
      pure res
  | otherwise = error "select: box (this is a bug)"
boxToBlock _ delayMap (LBDelay _ retBoxIndex)
  | Just delayLocal <- M.lookup retBoxIndex delayMap = pure delayLocal
  | otherwise = error "delay (this is a bug)"
boxToBlock env delayMap (LBCall n argBoxIndices) = do
  -- Evaluate all arguments to locals first
  argLocals <- sequence
    [ case M.lookup argBoxIndex env of
        Just box -> boxToBlockMemo env delayMap argBoxIndex box
        Nothing -> error "call: arg box not found (this is a bug)"
    | argBoxIndex <- argBoxIndices
    ]
  
  -- Push all arguments onto the stack right before the call
  sequence_ [emit $ ILocalGet argLocal | argLocal <- argLocals]
  
  -- Call function (args are on stack)
  emit $ ICall n
  
  -- Store result
  res <- localSimple
  emit $ ILocalSet res
  pure res

boxToBlockMemo :: Map BoxIndex LBox -> Map BoxIndex LocalIndex -> BoxIndex -> LBox -> CodegenM LocalIndex
boxToBlockMemo env delayMap k lbox = memoBox k (boxToBlock env delayMap lbox)

--------------------------------------------------------------------------------

codegen :: Expr -> (LocalIndex, [LocalIndex], [Instr])
codegen expr = (retLocal, finalEnv.locals, instrs)
  where
    -- Merge nested selects before generating boxes
    mergedExpr = mergeSelects expr
    (boxIndex, (_, boxMap)) = ST.runState (exprToBox mempty mergedExpr) (BoxIndex 0, mempty)
    Just box = M.lookup boxIndex boxMap

    initialEnv = CodegenEnv
      { nextLocal = LocalIndex 0
      , nextMem = MemAddr 0
      , values = mempty
      , locals = []
      }

    ((retLocal, finalEnv), instrs) = 
      W.runWriter (ST.runStateT gen initialEnv)

    gen :: CodegenM LocalIndex
    gen = do
      delayMap <- gatherDelays boxMap
      -- Initialize delay variables to 0

      -- TODO: not sure if needed, but in any case, do in a separate INIT sections
      -- otherwise we'll clear the delays every frame

      -- sequence_
      --   [ do
      --       emit $ IConst (I 0)
      --       emit $ ILocalSet delayLocal
      --   | delayLocal <- M.elems delayMap
      --   ]

      retLocal <- boxToBlockMemo boxMap delayMap boxIndex box
      emitDelays delayMap
      pure retLocal

--------------------------------------------------------------------------------
-- Test expressions

-- Simple expression: 5 + 10
testSimple :: Expr
testSimple = ECall (Ident "add") [EConst (I 5), EConst (I 10)]

testArr :: Expr
testArr = ESelect [3] (EArr [3] [EConst (I 1), EConst (I 2), EConst (I 3)]) [IdxConst 0]

-- More complex expression with delay and array
-- rec |prev| -> prev + [1, 2, 3][0]
testComplex :: Expr
testComplex = ERec 1 (Ident "prev") $
  ECall (Ident "add")
    [ EVar (Ident "prev")
    , ESelect [3] (EArr [3] [EConst (I 1), EConst (I 2), EConst (I 3)]) [IdxConst 0]
    ]

-- Expression with nested arrays and selection
-- [[1, 2], [3, 4]][1][0]
testNestedArray :: Expr
testNestedArray = ESelect [2]
  (ESelect [2, 2]
    (EArr [2, 2]
      [ EConst (I 1), EConst (I 2)
      , EConst (I 3), EConst (I 4)
      ])
    [IdxConst 1])
  [IdxConst 0]

-- Expression with nested arrays and selection
-- [[[0, 1], [2, 3]], [[4, 5], [5, 6]]][1][0][2]
testNestedArray2 :: Expr
testNestedArray2 = ESelect [2]
  (ESelect [2, 2]
    (EArr [2, 2]
      [ EConst (I 1), EConst (I 2)
      , EConst (I 3), EConst (I 4)
      ])
    [IdxConst 1])
  [IdxConst 0]

-- Expression with variable indexing
-- rec |i| -> arr[i] where arr = [10, 20, 30]
testVarIndex :: Expr
testVarIndex = ERec 1 (Ident "i") $
  ESelect [3]
    (EArr [3] [EConst (I 1), EConst (I 2), EConst (I 0)])
    [IdxVar (EVar (Ident "i"))]

runTestVarIndex :: (Maybe Number, MState)
runTestVarIndex = interpet (retIndex, locals, instrs <> instrs <> instrs <> instrs)
  where
    (retIndex, locals, instrs) = codegen testVarIndex

printBoxes :: Expr -> IO ()
printBoxes expr = do
  putStrLn $ "Box index: " ++ show boxIndex
  putStrLn "Boxes:"
  mapM_ (putStrLn . ("  " ++) . show) (M.toList boxMap)
  where
    (boxIndex, (_, boxMap)) = ST.runState (exprToBox mempty expr) (BoxIndex 0, mempty)

printCodegen :: String -> Expr -> IO ()
printCodegen name expr = do
  putStrLn $ "\n=== " ++ name ++ " ==="
  putStrLn $ "Expression: " ++ show expr
  let (LocalIndex retIdx, _, instrs) = codegen expr
  putStrLn $ "Return local: " ++ show retIdx
  putStrLn "Instructions:"
  mapM_ (putStrLn . ("  " ++) . show) instrs

runTests :: IO ()
runTests = do
  putStrLn "Testing OSC.Box codegen"
  printCodegen "Simple: 5 + 10" testSimple
  printCodegen "Complex: rec with delay and array select" testComplex
  printCodegen "Nested array selection" testNestedArray
  printCodegen "Variable indexing with delay" testVarIndex
