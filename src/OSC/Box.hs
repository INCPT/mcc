{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
-- {-# OPTIONS_GHC -fno-defer-type-errors #-}

module OSC.Box where

import Control.Monad (when)
import qualified Control.Monad.Reader as R
import Control.Monad.Reader (ReaderT)
import qualified Control.Monad.State as ST
import Control.Monad.State.Lazy (State, StateT)
import qualified Control.Monad.Writer.CPS as W
import Control.Monad.Writer.CPS (Writer)
import Data.Maybe (isJust)
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE

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
-- TODO: have --max-locals/--max-globals options; if exhausted, go to mem

-- TODO: should this be legal: f: f32[4] -> f32, rec |prev| return (f prev)

data Index a = IdxConst Int | IdxVar a
  deriving (Show, Functor, Foldable, Traversable)

data Expr'
  = EConst' Number
  | EVar' Ident
  | EGraphCall' Ident [Expr]
  | ECall' Ident [Expr]
  | EArr' [Expr']
  | ESelect' Expr (Index Ident)
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

data Type = TNumber | TArray Type Int -- dimension
  deriving Show

data Expr
  = EConst Number
  | EEmbedGraph Type Ident [Expr]
  | EVar Type Ident
  | EArr Type [Expr]
  | ESelect Type Expr (Index Expr)
  | ERec Type Int Ident Expr -- rec delay |prev| -> expr
  | ECall Type Ident [Expr]
  deriving Show

data Value = VNum Number | VArr [Value] -- start, length, unused dims
  deriving Show

interpretE :: Expr -> Maybe Value
interpretE = interpretE' mempty
  where
    interpretE' :: Map Ident Value -> Expr -> Maybe Value
    interpretE' _ (EConst n) = Just (VNum n)
    interpretE' env (EVar _ ident)
      | Just val <- M.lookup ident env = Just val
      | otherwise = Nothing  -- undefined variable
    interpretE' env (EArr _ exprs) = do
      vals <- traverse (interpretE' env) exprs
      Just (VArr vals)
    interpretE' env (ESelect _ expr index) = do
      val <- interpretE' env expr
      pure $ select env index val
    interpretE' env (ERec _ _ ident retExpr) = 
      -- For recursive expressions with delay, we need to iterate
      -- Start with 0 as the initial value for the delay variable
      let initialEnv = M.insert ident (VNum (I 0)) env
      in interpretE' initialEnv retExpr
    interpretE' env (ECall _ (Ident "add") [a, b]) = do
      VNum aVal <- interpretE' env a
      VNum bVal <- interpretE' env b
      Just $ VNum $ evalBinOp Plus aVal bVal
    interpretE' env (ECall _ (Ident "sub") [a, b]) = do
      VNum aVal <- interpretE' env a
      VNum bVal <- interpretE' env b
      Just $ VNum $ evalBinOp Minus aVal bVal
    interpretE' env (ECall _ (Ident "mul") [a, b]) = do
      VNum aVal <- interpretE' env a
      VNum bVal <- interpretE' env b
      Just $ VNum $ evalBinOp Mul aVal bVal
    interpretE' env (ECall _ (Ident "div") [a, b]) = do
      VNum aVal <- interpretE' env a
      VNum bVal <- interpretE' env b
      Just $ VNum $ evalBinOp Div aVal bVal
    interpretE' _ (ECall _ _ _) = Nothing  -- unknown function

    select :: Map Ident Value -> Index Expr -> Value -> Value
    select _ (IdxConst n) (VArr arr) = arr !! n
    select env (IdxVar expr) (VArr arr)
      | Just (VNum (I n)) <- interpretE' env expr = arr !! n
      | otherwise = error "select: index not an integer"
    select _ _ _ = error "select: not an array"

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
  | LBGlobal Type Ident [Index BoxIndex] -- indices; no indices means value
  | LBArr Type [BoxIndex]
  | LBSelect Type BoxIndex (Index BoxIndex)
  | LBRec Type Int Ident BoxIndex
  | LBCall Type Ident [BoxIndex]
  deriving Show

-- inlineRef :: Ident -> Expr -> Expr -> Expr
-- inlineRef n replace expr = inline expr
--   where
--     inline (EVar t v)
--       | v == n = replace
--       | otherwise = EVar t v
--     inline e@(EConst _) = e
--     inline (EArr t es) = EArr t (map inline es)
--     inline (ESelect t e is) = ESelect t (inline e) (map (fmap inline) is)
--     inline (ERec t delay v ret)
--       | v == n = ERec t delay v ret  -- shadowed, don't recurse
--       | otherwise = ERec t delay v (inline ret)
--     inline (ECall t f args) = ECall t f (map inline args)

-- TODO: steps
-- * typecheck
-- ** is it possible to only type annotate arguments (and maybe return values) and have everything else be inferred?
-- * var names -> indices, SSA
-- * check for recursion
-- * simplify, fusion rules, find fixpoint
-- ** fusion .e.g fold . map = fold with folded map inside :D
-- ** (ERec _ _ _ (EConst n)) = n
-- ** (ESelect [a, b, c])[1] = b
-- * constant folding (also fold compile time constants like $voices)
-- * cluster common subexpressions
-- * if cluster referenced only once, inline
-- ** have a configurable max inline function size
-- * if something is not referenced in delay, don't alloc delay box and compute it lazily in e.g. select
-- ** e.g. bindings that do not reference the recusive head can be outside the rec block
-- * codegen
-- ** choice strategy: for small choice tables (e.g. < 5) use ifs

exprToBox :: Expr -> BoxGenM BoxIndex
exprToBox (EConst n) = newBox (LBConst n)
exprToBox (EVar t n) = newBox (LBVar t n)
-- exprToBox (ERec _ _ _ (EConst n)) = newBox (LBConst n) -- TODO: do this in a simplify pass
exprToBox (ERec t delay n ret) = mdo
  retBoxIndex <- exprToBox ret
  newBox (LBRec t delay n retBoxIndex)
exprToBox (EArr t es) = do
  labels <- traverse exprToBox es
  newBox (LBArr t labels)
exprToBox (ESelect t e idx) = do
  newBox =<< (LBSelect <$> pure t <*> exprToBox e <*> sequenceA (fmap exprToBox idx))
exprToBox (ECall t n args) = do
  argBoxIndexs <- traverse exprToBox args
  newBox (LBCall t n argBoxIndexs)

--------------------------------------------------------------------------------

-- an eval tree returns either a const or an array of consts
-- const goes in known local
-- array goes in knowb base addr
-- in the case of RCall this means that arguments can be arrays and return values as well
-- no need to pass anything on stack then; unless we want to reuse wasm from global function and pass args and return values on stack

-- calling convention:
-- simple values are passed/returned on stack
-- array arg baseAddrs are known statically; inline in codegen
-- array returns baseAddrs are knowb statically as well; inline in codegen
-- in case of function calls (e.g. something can't be inlined), pass and return array baseAddrs on stack

-- FTree doesn't care about calling conventions! but inlcude the types so the AGenM monad can then generate calling convention code

data FTree r e = FLeaf r | FChoice [FTree r e] r

data R = RConst Number | RArr [R] | RCall Ident [R]

one (fidx :| []) = fidx
one _ = error "funcrefs: ESelect: one (this is a bug)"

funcrefs :: Expr -> NE.NonEmpty (FTree R Expr)
funcrefs e@(EConst n) = FLeaf (RConst n) [] :| []
-- funcrefs (EArr _ es) = mconcat (fmap funcrefs es)
-- funcrefs (ESelect _ (EArr _ es) (IdxVar idx)) = FTree (concatMap NE.toList $ fmap funcrefs es) (one $ funcrefs idx) :| []
-- funcrefs (ESelect _ e (IdxVar idx)) = FTree (NE.toList $ funcrefs e) (one $ funcrefs idx) :| []

-- funcrefs' :: Expr -> FTree Expr
-- funcrefs' (EArr _ es) = undefined -- impossible
-- funcrefs' (ESelect _ (EArr _ es) (IdxVar idx)) = FTree (map funcrefs' es) idx
-- funcrefs' (ESelect _ e (IdxVar idx)) = FTree [funcrefs' e] idx

-- TODO: AGenM should have two instances
-- ** one with locals
-- ** one with memory

-- this way the same (pure) function can be used in graph and normal code

peelOff :: Type -> Type
peelOff TNumber = error "peelOff: number"
peelOff (TArray t _) = t

boxToA :: LBox -> AGenM Number ()
boxToA (LBConst n) = write n
boxToA (LBSelect (TArray _ dim) innerIndex (IdxVar idx)) = do
  inner <- getBox innerIndex

  case inner of
    LBConst _ -> error "select: const"
    LBGlobal t n indices -> sequence_
      [ at i $ boxToA (LBGlobal (peelOff t) n (indices <> [IdxConst i]))
      | i <- [0..dim-1] 
      ]
    LBArr _ elems -> do
      frefs <- sequence
        [ funcRef elemIndex (boxToA =<< getBox elemIndex)
        | elemIndex <- elems
        ]

      onStack $ boxToA =<< getBox idx
      goto frefs
    LBSelect t innerIndex' idx -> do
      undefined

  undefined
    -- LBRec TNumber delay ident retIndex -> do
    --   retLocal <- allocLocal
    --   valueLocal <- allocLocal
    --   ST.modify $ \st -> st { aDelays = (delay, RefLocal valueLocal, RefLocal retLocal):st.aDelays }
    --   R.local (\env -> env { aDelayMap = M.insert ident (RefLocal retLocal) env.aDelayMap }) $ do
    --     boxToA retIndex
    --     -- Result is now on the stack
    --     storeStackToLocalAndLeaveOnStack valueLocal
    -- _ -> undefined
  
-- data AGenEnv = AGenEnv
--   { boxMap :: Map BoxIndex LBox
--   }

-- data AGenSt = AGenSt
--   { aNextLocal :: LocalIndex
--   , aNextMem :: MemAddr
--   , aDelays :: [(Int, Ref, Ref)]
--   }
-- 
-- data AGenEnv = AGenEnv
--   { aBoxMap :: Map BoxIndex LBox
--   , aDelayMap :: Map Ident Ref
--   }

data FuncRef

data AGenM t a = AGenM

write :: t -> AGenM t ()
write = undefined

at :: Int -> AGenM t () -> AGenM t ()
at = undefined

-- TODO: this isn't portable (e.g. GPU)
onStack :: AGenM t () -> AGenM t ()
onStack = undefined

-- creates and caches a func ref
-- the created function expects the array context as an argument so the function can be called from different contexts
funcRef :: BoxIndex -> AGenM t () -> AGenM t FuncRef
funcRef = undefined

-- expects the selector to be on the stack
-- passes the array context to each funcref
goto :: [FuncRef] -> AGenM t ()
goto = undefined

getBox :: BoxIndex -> AGenM t LBox
getBox idx = do
  m <- R.ask
  case M.lookup idx m.aBoxMap of
    Just box -> pure box
    Nothing -> error "getBox (this is a bug)"

--------------------------------------------------------------------------------

-- TODO: after component clustering, if a component is called only once, inline

newtype LocalIndex = LocalIndex Int
  deriving (Num, Eq, Ord, Show)

newtype MemAddr = MemAddr Int
  deriving (Num, Eq, Ord, Show)

data Return = Stack | BasePtr LocalIndex
  deriving (Eq, Show)

data BinOp = Plus | Mul | Minus | Div deriving Show

data Instr
  = ILocalGet LocalIndex
  | ILocalSet LocalIndex
  | ILocalTee LocalIndex  -- set and leave value on stack
  | Swap  -- swap top two stack values
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

interpret :: (Return, [LocalIndex], [Instr]) -> (Maybe Number, MState)
interpret (retValue, locals, instrs) = (result, state)
  where
    state = go (emptyMState { locals = M.fromList (fmap (, I 0) locals) }) instrs
    
    result = case retValue of
      Stack -> case state.stack of
        (val:_) -> Just val
        [] -> Nothing
      BasePtr localIdx -> 
        -- The local contains the base address, look it up in memory
        case M.lookup localIdx state.locals of
          Just (I addr) -> M.lookup (MemAddr addr) state.memory
          _ -> Nothing

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
      
      Swap ->
        case res.stack of
          (a:b:stackRest) ->
            go (res { stack = b : a : stackRest }) rest
          _ -> error "Stack underflow on Swap"
      
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

data EvalContext = EvalContext
  { arrayBasePtr :: Maybe LocalIndex
  , delayMap :: Map BoxIndex LocalIndex
  }

data MemoKey = MemoKey BoxIndex Bool
  deriving (Eq, Ord)

data CodegenEnv = CodegenEnv
  { nextLocal :: LocalIndex
  , nextMem :: MemAddr
  , values :: Map MemoKey Return
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

memoBox :: BoxIndex -> Bool -> CodegenM Return -> CodegenM Return
memoBox boxIndex inArrayCtx genReturn = do
  env <- ST.get
  let key = MemoKey boxIndex inArrayCtx
  case M.lookup key env.values of
    Just ret -> pure ret
    Nothing -> mdo
      -- This works because the state is lazy; we update the state first here because
      -- genReturn is recursive and won't return and thus the state will be updated
      -- only at the end
      ST.put $ env { values = M.insert key ret env.values }
      ret <- genReturn
      pure ret

emit :: Instr -> CodegenM ()
emit = W.tell . pure

-- gatherDelays :: Map BoxIndex LBox -> CodegenM (Map BoxIndex LocalIndex)
-- gatherDelays boxMap = M.fromList <$> sequence
--   [ (retBoxIndex,) <$> localSimple
--   | LBDelay _ _ retBoxIndex <- M.elems boxMap
--   ]
-- 
-- emitDelays :: Map BoxIndex LBox -> EvalContext -> Map BoxIndex Return -> CodegenM ()
-- emitDelays boxMap ctx returnMap = do
--   sequence_
--     [ case M.lookup retBoxIndex returnMap of
--         Just Stack -> do
--           -- Value is on stack, store it in delay local
--           emit $ ILocalSet delayLocal
--         Just (BasePtr ptr) -> do
--           -- Array pointer, store it in delay local
--           emit $ ILocalGet ptr
--           emit $ ILocalSet delayLocal
--         Nothing -> error "emitDelays: return value not found (this is a bug)"
--     | LBDelay _ _ retBoxIndex <- M.elems boxMap
--     , Just delayLocal <- [M.lookup retBoxIndex ctx.delayMap]
--     ]

sizeOfType :: Type -> Int
sizeOfType TNumber = 4
sizeOfType (TArray t dim) = sizeOfType t * dim

isSimpleType :: Type -> Bool
isSimpleType TNumber = True
isSimpleType (TArray _ _) = False

-- boxToBlock :: Map BoxIndex LBox -> EvalContext -> LBox -> CodegenM Return
-- boxToBlock _ ctx (LBConst n) = 
--   case ctx.arrayBasePtr of
--     Nothing -> do
--       -- Put value on stack
--       emit $ IConst n
--       pure Stack
--     Just basePtr -> do
--       -- Write to array
--       emit $ ILocalGet basePtr
--       emit $ IConst n
--       emit $ IStore (MemAddr 0)
--       pure $ BasePtr basePtr
-- 
-- boxToBlock _ ctx (LBVar _ ident) = 
--   case ctx.arrayBasePtr of
--     Nothing -> do
--       -- Put value on stack
--       emit $ IGlobalGet ident
--       pure Stack
--     Just basePtr -> do
--       -- Write to array
--       emit $ ILocalGet basePtr
--       emit $ IGlobalGet ident
--       emit $ IStore (MemAddr 0)
--       pure $ BasePtr basePtr
-- boxToBlock env ctx (LBArr arrayType boxes) = do
--   let totalSize = sizeOfType arrayType
--   basePtr <- case ctx.arrayBasePtr of
--     Nothing -> fst <$> localArray totalSize
--     Just ptr -> pure ptr
--   
--   -- Evaluate elements with array context
--   sequence_
--     [ do
--         let offset = idx * 4  -- 4 bytes per element for now
--         offsetPtr <- localSimple
--         emit $ ILocalGet basePtr
--         emit $ IConst (I offset)
--         emit $ IBinOp Plus
--         emit $ ILocalSet offsetPtr
--         
--         let elemCtx = ctx { arrayBasePtr = Just offsetPtr }
--         case M.lookup boxIndex env of
--           Just box -> boxToBlockMemo env elemCtx boxIndex box
--           Nothing -> error "LBArr: box not found (this is a bug)"
--     | (idx, boxIndex) <- zip [0..] boxes
--     ]
--   
--   pure $ BasePtr basePtr
-- 
-- -- boxToBlock env ctx (LBSelect selectType boxIndex indices)
-- --   | Just box <- M.lookup boxIndex env = do
-- --       -- Calculate offset from indices
-- --       offsetLocal <- localSimple
-- --       emit $ IConst (I 0)
-- --       emit $ ILocalSet offsetLocal
-- --       
-- --       sequence_
-- --         [ case idx of
-- --             IdxConst 0 -> pure ()
-- --             IdxConst i -> do
-- --               emit $ ILocalGet offsetLocal
-- --               emit $ IConst (I (i * 4))  -- 4 bytes per element
-- --               emit $ IBinOp Plus
-- --               emit $ ILocalSet offsetLocal
-- --             IdxVar indexBoxIndex
-- --               | Just indexBox <- M.lookup indexBoxIndex env -> do
-- --                   let indexCtx = ctx { arrayBasePtr = Nothing }
-- --                   indexRet <- boxToBlockMemo env indexCtx indexBoxIndex indexBox
-- --                   case indexRet of
-- --                     Stack -> do
-- --                       -- Index value is on stack
-- --                       emit $ IConst (I 4)
-- --                       emit $ IBinOp Mul
-- --                       emit $ ILocalGet offsetLocal
-- --                       emit $ IBinOp Plus
-- --                       emit $ ILocalSet offsetLocal
-- --                     _ -> error "select: index must be simple type (this is a bug)"
-- --               | otherwise -> error "select: index box not found (this is a bug)"
-- --         | idx <- indices
-- --         ]
-- --       
-- --       if isSimpleType selectType then
-- --         case ctx.arrayBasePtr of
-- --           Nothing -> do
-- --             -- Read value and put on stack
-- --             sourceRet <- boxToBlockMemo env (ctx { arrayBasePtr = Nothing }) boxIndex box
-- --             case sourceRet of
-- --               BasePtr sourcePtr -> do
-- --                 emit $ ILocalGet sourcePtr
-- --                 emit $ ILocalGet offsetLocal
-- --                 emit $ IBinOp Plus
-- --                 emit $ ILoad (MemAddr 0)
-- --                 pure Stack
-- --               _ -> error "select: source must be array (this is a bug)"
-- --           Just destPtr -> do
-- --             -- Read value and write to destination
-- --             sourceRet <- boxToBlockMemo env (ctx { arrayBasePtr = Nothing }) boxIndex box
-- --             case sourceRet of
-- --               BasePtr sourcePtr -> do
-- --                 emit $ ILocalGet destPtr
-- --                 emit $ ILocalGet sourcePtr
-- --                 emit $ ILocalGet offsetLocal
-- --                 emit $ IBinOp Plus
-- --                 emit $ ILoad (MemAddr 0)
-- --                 emit $ IStore (MemAddr 0)
-- --                 pure $ BasePtr destPtr
-- --               _ -> error "select: source must be array (this is a bug)"
-- --       else
-- --         -- Result is array type
-- --         case ctx.arrayBasePtr of
-- --           Nothing -> do
-- --             -- Allocate destination array
-- --             let arraySize = sizeOfType selectType
-- --             (destPtr, _) <- localArray arraySize
-- --             
-- --             -- Evaluate source with adjusted pointer
-- --             sourceRet <- boxToBlockMemo env (ctx { arrayBasePtr = Nothing }) boxIndex box
-- --             case sourceRet of
-- --               BasePtr sourcePtr -> do
-- --                 -- Copy from source + offset to destination
-- --                 -- For now, just pass adjusted pointer to source
-- --                 adjustedPtr <- localSimple
-- --                 emit $ ILocalGet sourcePtr
-- --                 emit $ ILocalGet offsetLocal
-- --                 emit $ IBinOp Plus
-- --                 emit $ ILocalSet adjustedPtr
-- --                 
-- --                 let adjustedCtx = ctx { arrayBasePtr = Just destPtr }
-- --                 -- TODO: need to actually copy or re-evaluate
-- --                 pure $ BasePtr destPtr
-- --               _ -> error "select: source must be array (this is a bug)"
-- --           Just destPtr -> do
-- --             -- Pass down adjusted destination pointer
-- --             adjustedDestPtr <- localSimple
-- --             emit $ ILocalGet destPtr
-- --             emit $ ILocalGet offsetLocal
-- --             emit $ IBinOp Plus
-- --             emit $ ILocalSet adjustedDestPtr
-- --             
-- --             let adjustedCtx = ctx { arrayBasePtr = Just adjustedDestPtr }
-- --             boxToBlockMemo env adjustedCtx boxIndex box
-- --   | otherwise = error "select: box not found (this is a bug)"
-- -- boxToBlock _ ctx (LBDelay _ _ retBoxIndex)
-- --   | Just delayLocal <- M.lookup retBoxIndex ctx.delayMap = 
-- --       case ctx.arrayBasePtr of
-- --         Nothing -> do
-- --           emit $ ILocalGet delayLocal
-- --           pure Stack
-- --         Just basePtr -> do
-- --           emit $ ILocalGet basePtr
-- --           emit $ ILocalGet delayLocal
-- --           emit $ IStore (MemAddr 0)
-- --           pure $ BasePtr basePtr
-- --   | otherwise = error "delay: not found in delayMap (this is a bug)"
-- boxToBlock env ctx (LBCall _ ident argBoxIndices) = do
--   -- Evaluate all arguments (they should be simple types on stack)
--   sequence_
--     [ case M.lookup argBoxIndex env of
--         Just box -> do
--           let argCtx = ctx { arrayBasePtr = Nothing }
--           ret <- boxToBlockMemo env argCtx argBoxIndex box
--           case ret of
--             Stack -> pure ()  -- Already on stack
--             _ -> error "call: argument must be simple type (this is a bug)"
--         Nothing -> error "call: arg box not found (this is a bug)"
--     | argBoxIndex <- argBoxIndices
--     ]
--   
--   -- Call function (args are on stack, result will be on stack)
--   emit $ ICall ident
--   
--   case ctx.arrayBasePtr of
--     Nothing -> pure Stack
--     Just basePtr -> do
--       -- Store result to array
--       emit $ ILocalGet basePtr
--       emit $ Swap  -- TODO: might need a temp local instead
--       emit $ IStore (MemAddr 0)
--       pure $ BasePtr basePtr
-- 
-- boxToBlockMemo :: Map BoxIndex LBox -> EvalContext -> BoxIndex -> LBox -> CodegenM Return
-- boxToBlockMemo env ctx boxIndex lbox = 
--   memoBox boxIndex (isJust ctx.arrayBasePtr) (boxToBlock env ctx lbox)
-- 
-- --------------------------------------------------------------------------------
-- 
-- -- TODO: test nested recs etc
-- 
-- -- TODO: figure out nested indices
-- -- TODO: generate random but valid Exprs and compare output with codegen
-- -- TODO: be able to specify iterations too (for recursive outputs)
-- 
-- codegen :: Expr -> (Return, [LocalIndex], [Instr])
-- codegen expr = (retValue, finalEnv.locals, instrs)
--   where
--     (boxIndex, (_, boxMap)) = ST.runState (exprToBox mempty expr) (BoxIndex 0, mempty)
--     Just box = M.lookup boxIndex boxMap
-- 
--     initialEnv = CodegenEnv
--       { nextLocal = LocalIndex 0
--       , nextMem = MemAddr 0
--       , values = mempty
--       , locals = []
--       }
-- 
--     ((retValue, finalEnv), instrs) = 
--       W.runWriter (ST.runStateT gen initialEnv)
-- 
--     gen :: CodegenM Return
--     gen = do
--       delayMap <- gatherDelays boxMap
--       
--       let ctx = EvalContext
--             { arrayBasePtr = Nothing
--             , delayMap = delayMap
--             }
--       
--       retValue <- boxToBlockMemo boxMap ctx boxIndex box
--       
--       -- Collect all return values for delay emission
--       returnMap <- ST.gets values
--       let returnsByBox = M.fromList
--             [ (bi, ret)
--             | (MemoKey bi _, ret) <- M.toList returnMap
--             ]
--       
--       emitDelays boxMap ctx returnsByBox
--       pure retValue
-- 
-- --------------------------------------------------------------------------------
-- -- Test expressions
-- 
-- -- Simple expression: 5 + 10
-- -- testSimple :: Expr
-- -- testSimple = ECall TNumber (Ident "add") [EConst (I 5), EConst (I 10)]
-- -- 
-- -- testArr :: Expr
-- -- testArr = ESelect TNumber [3] (EArr (TArray [TNumber] 3) [EConst (I 1), EConst (I 2), EConst (I 3)]) [IdxConst 1]
-- -- 
-- -- -- More complex expression with delay and array
-- -- -- rec |prev| -> prev + [1, 2, 3][1]
-- -- testComplex :: Expr
-- -- testComplex = ERec TNumber 1 (Ident "prev") $
-- --   ECall TNumber (Ident "add")
-- --     [ EVar TNumber (Ident "prev")
-- --     , ESelect TNumber [3] (EArr (TArray [TNumber] 3) [EConst TNumber (I 1), EConst TNumber (I 2), EConst TNumber (I 3)]) [IdxConst 1]
-- --     ]
-- -- 
-- -- -- Expression with nested arrays and selection
-- -- -- [[1, 2], [3, 4]][1][0]
-- -- testNestedArray :: Expr
-- -- testNestedArray = ESelect TNumber [2]
-- --   (ESelect (TArray [TNumber] 2) [2, 2]
-- --     (EArr (TArray [TArray [TNumber] 2] 2)
-- --       [ EArr (TArray [TNumber] 2) [EConst TNumber (I 1), EConst TNumber (I 2)]
-- --       , EArr (TArray [TNumber] 2) [EConst TNumber (I 3), EConst TNumber (I 4)]
-- --       ])
-- --     [IdxConst 1])
-- --   [IdxConst 0]
-- -- 
-- -- -- Expression with nested arrays and selection
-- -- -- [[[0, 1], [2, 3]], [[4, 5], [6, 7]]][1][0][0]
-- -- testNestedArray2 :: Expr
-- -- testNestedArray2 = ESelect TNumber [2]
-- --   (ESelect (TArray [TNumber] 2) [2, 2, 2]
-- --     (EArr (TArray [TNumber, TNumber, TNumber] 8)
-- --       [ EConst TNumber (I 0), EConst TNumber (I 1)
-- --       , EConst TNumber (I 2), EConst TNumber (I 3)
-- --       , EConst TNumber (I 4), EConst TNumber (I 5)
-- --       , EConst TNumber (I 6), EConst TNumber (I 7)
-- --       ])
-- --     [IdxConst 1, IdxConst 1])
-- --   [IdxConst 0]
-- -- 
-- -- -- Expression with variable indexing
-- -- -- rec |i| -> arr[i] where arr = [1, 2, 3]
-- -- testVarIndex :: Expr
-- -- testVarIndex = ERec TNumber 1 (Ident "i") $
-- --   ESelect TNumber [3]
-- --     (EArr (TArray [TNumber] 3) [EConst TNumber (I 1), EConst TNumber (I 2), EConst TNumber (I 0)])
-- --     [IdxVar (EVar TNumber (Ident "i"))]
-- 
-- -- runTestVarIndex :: (Maybe Number, MState)
-- -- runTestVarIndex = interpret (retIndex, locals, instrs <> instrs <> instrs <> instrs)
-- --   where
-- --     (retIndex, locals, instrs) = codegen testVarIndex
-- 
-- printBoxes :: Expr -> IO ()
-- printBoxes expr = do
--   putStrLn $ "Box index: " ++ show boxIndex
--   putStrLn "Boxes:"
--   mapM_ (putStrLn . ("  " ++) . show) (M.toList boxMap)
--   where
--     (boxIndex, (_, boxMap)) = ST.runState (exprToBox mempty expr) (BoxIndex 0, mempty)
-- 
-- printCodegen :: String -> Expr -> IO ()
-- printCodegen name expr = do
--   putStrLn $ "\n=== " ++ name ++ " ==="
--   putStrLn $ "Expression: " ++ show expr
--   let (retValue, _, instrs) = codegen expr
--   putStrLn $ "Return value: " ++ show retValue
--   putStrLn "Instructions:"
--   mapM_ (putStrLn . ("  " ++) . show) instrs
-- 
-- -- runTests :: IO ()
-- -- runTests = do
-- --   putStrLn "Testing OSC.Box codegen"
-- --   printCodegen "Simple: 5 + 10" testSimple
-- --   printCodegen "Complex: rec with delay and array select" testComplex
-- --   printCodegen "Nested array selection" testNestedArray
-- --   printCodegen "Variable indexing with delay" testVarIndex
