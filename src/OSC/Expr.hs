{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}

module OSC.Expr where

import Control.Monad (when)
import qualified Control.Monad.Except as E
import qualified Control.Monad.Reader as R
import qualified Control.Monad.State as ST

import Data.Bits ((.&.), (.|.), xor, shiftL, shiftR, rotateL, rotateR)
import Data.List (intercalate)
import Data.Generics.Uniplate.Data (universe)

import qualified Data.Graph as G
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import OSC.Ctx hiding (push, pop)
import OSC.Call

newtype TypeError = TypeError String
  deriving Show

type GenM = E.ExceptT TypeError (R.Reader (Map Ident Type))

-- Helper function to copy the sign from one float to another
copySign :: (RealFloat a) => a -> a -> a
copySign x y = if signum y < 0 then negate (abs x) else abs x

lookupE :: Ord k => String -> M.Map k v -> k -> v
lookupE e m k = case M.lookup k m of
  Just v -> v
  Nothing -> error e

topsort :: Ord node => (a -> Set node) -> [(node, a)] -> Either [G.Tree G.Vertex] [(node, a)]
topsort nodeEdges nodes
  | hasCycles = Left (G.scc graph)
  | otherwise = Right [ (n, lookupE "topsort" nodesMap n) | v <- reverse (G.topSort graph), let (_, n, _) = nodeFromVertex v ]
  where
    nodesMap = M.fromList nodes

    edges = [ (node, node, S.toList (nodeEdges a)) | (node, a) <- nodes ]
    (graph, nodeFromVertex, _) = G.graphFromEdges edges

    hasCycles :: Bool
    hasCycles = or [ isCycle node | node <- G.scc graph ]
      where
        isCycle (G.Node _ []) = False  -- single node SCC = no cycle
        isCycle (G.Node _ _) = True    -- multi-node SCC = cycle

reccheck :: [(Ident, Expr ())] -> Either TypeError [(Ident, Expr ())]
reccheck bindings = case topsort (\expr -> S.fromList [ n | EVar _ n <- universe expr ]) bindings of
  Left scc -> Left $ TypeError $ "reccheck: cyclic dependency involving: " <> show scc
  Right bindings' -> Right bindings'

dupcheck :: [(Ident, Expr ())] -> Maybe TypeError
dupcheck bindings
  | null dups = Nothing
  | otherwise = Just $ TypeError $ "dupcheck: duplicate bindings: " <> show dups
  where
    counts = M.fromListWith (+) ((, 1 :: Int) <$> fmap fst bindings)
    dups = [ n | (n, x) <- M.toList counts, x > 1 ]

-- NOTE: we could theoretically do the typechecking after transforming to CExpr and save a bit of work,
-- but that'd make everything more convoluted and it would make interpreting Exprs for testing potentially
-- harder since we wouldn't have type information

-- NOTE: for future reference: https://blog.stimsina.com/post/implementing-a-hindley-milner-type-system-part-2

-- TODO: allow shadowing only if exprs of different type?
---- this means shadowcheck must happen after typechecking
---- and also in reccheck we can't indiscriminately collect EVars; nested bindings must reset the reccheck

shadowcheck :: Map Ident (Expr ()) -> Maybe TypeError
shadowcheck = undefined

--------------------------------------------------------------------------------

treturnType :: E.MonadError TypeError m => Type -> m Type
treturnType (TAbs _ t) = pure t
treturnType t = E.throwError $ TypeError $ "returnType: not a function: " <> show t

tpeelType :: E.MonadError TypeError m => Type -> m Type
tpeelType (TArr t _) = pure t
tpeelType t = E.throwError $ TypeError $ "peelType: not an array: " <> show t

tparamTypes :: E.MonadError TypeError m => Type -> String -> m [Type]
tparamTypes (TAbs params _) _ = pure params
tparamTypes t e = E.throwError $ TypeError $ "paramTypes: not a function: " <> e <> ": " <> show t

typecheck :: Expr () -> GenM (Expr Type)
typecheck (EConst n) = pure $ EConst n

typecheck (EOp () op a b) = do
  a' <- typecheck a
  b' <- typecheck b

  let ta = exprType a'
  let tb = exprType b'

  case (op, ta, tb) of
    -- Arithmetic operations: return same type as operands
    (Add, TNumber t, TNumber u) | t == u -> pure $ EOp (TNumber t) op a' b'
    (Sub, TNumber t, TNumber u) | t == u -> pure $ EOp (TNumber t) op a' b'
    (Mul, TNumber t, TNumber u) | t == u -> pure $ EOp (TNumber t) op a' b'
    (Div, TNumber t, TNumber u) | t == u -> pure $ EOp (TNumber t) op a' b'
    (Mod, TNumber t, TNumber u) | t == u -> pure $ EOp (TNumber t) op a' b'
    (Rem, TNumber t, TNumber u) | t == u -> pure $ EOp (TNumber t) op a' b'
    (Min, TNumber t, TNumber u) | t == u -> pure $ EOp (TNumber t) op a' b'
    (Max, TNumber t, TNumber u) | t == u -> pure $ EOp (TNumber t) op a' b'
    (CopySign, TNumber t, TNumber u) | t == u -> pure $ EOp (TNumber t) op a' b'
    
    -- Bitwise operations: integer types only
    (And, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> pure $ EOp (TNumber t) op a' b'
    (Or, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> pure $ EOp (TNumber t) op a' b'
    (Xor, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> pure $ EOp (TNumber t) op a' b'
    (Shl, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> pure $ EOp (TNumber t) op a' b'
    (Shr, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> pure $ EOp (TNumber t) op a' b'
    (Rotl, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> pure $ EOp (TNumber t) op a' b'
    (Rotr, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> pure $ EOp (TNumber t) op a' b'
    
    -- Comparison operations: return I32 (boolean)
    (Eq, TNumber t, TNumber u) | t == u -> pure $ EOp (TNumber TI32) op a' b'
    (Ne, TNumber t, TNumber u) | t == u -> pure $ EOp (TNumber TI32) op a' b'
    (Gt, TNumber t, TNumber u) | t == u -> pure $ EOp (TNumber TI32) op a' b'
    (Lt, TNumber t, TNumber u) | t == u -> pure $ EOp (TNumber TI32) op a' b'
    (GEt, TNumber t, TNumber u) | t == u -> pure $ EOp (TNumber TI32) op a' b'
    (LEt, TNumber t, TNumber u) | t == u -> pure $ EOp (TNumber TI32) op a' b'
    
    -- Type mismatch error
    _ -> E.throwError $ TypeError $ "typecheck: " <> show op <> ": type mismatch: " <> show ta <> " and " <> show tb

typecheck (EArr () []) = E.throwError $ TypeError $ "typecheck: empty array"
typecheck (EArr () (a:as)) = do
  a' <- typecheck a
  as' <- traverse typecheck as
  let at = exprType a'
  if all ((== at) . exprType) as'
    then pure $ EArr (TArr at (length as + 1)) (a':as')
    else E.throwError $ TypeError $ "typecheck: mismatched types: " <> show (at:fmap exprType as')

typecheck (EVar () n) = fmap (M.lookup n) R.ask >>= \case
  Just t -> pure $ EVar t n
  Nothing -> E.throwError $ TypeError $ "typecheck: unknown binding: " <> show n

typecheck (EAbs t params bindings body) = do
  ptypes <- tparamTypes t "EAbs"
  rtype <- treturnType t

  let paramsEnv = M.fromList (zip params ptypes)

  bindings' <- R.local (\env -> paramsEnv <> env) $ typecheckBindings bindings
  body' <- R.local (\env -> M.fromList (fmap (fmap exprType) bindings') <> paramsEnv <> env) $ typecheck body
  
  when (exprType body' /= rtype) $ E.throwError $ TypeError $ "typecheck: function doesn't return the right type"
  
  pure $ EAbs t params bindings' body'

typecheck (EApp () f params) = do
  f' <- typecheck f
  params' <- traverse typecheck params

  ptypes <- tparamTypes (exprType f') "EApp"
  rtype <- treturnType (exprType f')

  when (length ptypes /= length params') $ E.throwError $ TypeError $ "typecheck: argument count doesn't match function definition"

  sequence_
    [ when (fpt /= pt) $ E.throwError $ TypeError $ "typecheck: type mismatch in function application: " <> show fpt <> " <=> " <> show pt
    | (fpt, pt) <- zip ptypes (fmap exprType params')
    ]

  pure $ EApp rtype f' params'

typecheck (ESelect () expr sel) = do
  expr' <- typecheck expr
  sel' <- typecheck sel

  t <- tpeelType (exprType expr')

  case exprType expr' of
    TArr _ _ -> pure ()
    t -> E.throwError $ TypeError $ "typecheck: lhs not an array: " <> show t
  
  case exprType sel' of
    TNumber TI32 -> pure ()
    TNumber TI64 -> pure ()
    t -> E.throwError $ TypeError $ "typecheck: selection index not an integer: " <> show t
  
  pure $ ESelect t expr' sel'

typecheck (ERec t delay param bindings body) = do
  when (delay <= 0) $ E.throwError $ TypeError $ "typecheck: delay must be > 0: " <> show delay

  let paramsEnv = M.singleton param t

  bindings' <- R.local (\env -> paramsEnv <> env) $ typecheckBindings bindings
  body' <- R.local (\env -> M.fromList (fmap (fmap exprType) bindings') <> paramsEnv <> env) $ typecheck body
  
  when (typeContainsAbs t) $ E.throwError $ TypeError $ "typecheck: return type contains functions: " <> show t
  when (exprType body' /= t) $ E.throwError $ TypeError $ "typecheck: return type differs from delay head: " <> show (t, exprType body')

  pure $ ERec t delay param bindings' body'
  where
    typeContainsAbs (TNumber _) = False
    typeContainsAbs (TArr t _) = typeContainsAbs t
    typeContainsAbs (TAbs _ _) = True

typecheckBindings :: [(Ident, Expr ())] -> GenM [(Ident, Expr Type)]
typecheckBindings bindings
  | Just e <- dupcheck bindings = E.throwError e
  | otherwise = case reccheck bindings of
      Left e -> E.throwError e
      Right sortedBindings -> go sortedBindings
        where
          go [] = pure []
          go ((n, expr):bs) = do
            expr' <- typecheck expr
            bs' <- R.local (\env -> M.singleton n (exprType expr') <> env) (go bs)
            return $ (n, expr'):bs'

infer :: Expr () -> Either TypeError (Expr Type)
infer = flip R.runReader mempty . E.runExceptT . typecheck

inferMany :: [(Ident, Expr ())] -> Either TypeError [(Ident, Expr Type)]
inferMany = flip R.runReader mempty . E.runExceptT . typecheckBindings

--------------------------------------------------------------------------------

i32 :: Int -> Expr ()
i32 = EConst . I32

f32 :: Float -> Expr ()
f32 = EConst . F32

i64 :: Int -> Expr ()
i64 = EConst . I64

f64 :: Double -> Expr ()
f64 = EConst . F64

op :: Op -> Expr () -> Expr () -> Expr ()
op = EOp ()

arr :: [Expr ()] -> Expr ()
arr = EArr ()

var :: Ident -> Expr ()
var = EVar ()

abs_ :: [(Ident, Type)] -> Type -> [(Ident, Expr ())] -> Expr () -> Expr ()
abs_ params rtype = EAbs (TAbs (fmap snd params) rtype) (fmap fst params)

app :: Expr () -> [Expr ()] -> Expr ()
app = EApp ()

sel :: Expr () -> Expr () -> Expr ()
sel = ESelect ()

rec_ :: Type -> Int -> Ident -> [(Ident, Expr ())] -> Expr () -> Expr ()
rec_ = ERec

--------------------------------------------------------------------------------

ti32 :: Type
ti32 = TNumber TI32

tf32 :: Type
tf32 = TNumber TF32

ti64 :: Type
ti64 = TNumber TI64

tf64 :: Type
tf64 = TNumber TF64

tarr :: Type -> Int -> Type
tarr = TArr

(-->) :: [Type] -> Type -> Type
(-->) = TAbs

(|:) :: Ident -> Type -> (Ident, Type)
(|:) = (,)

--------------------------------------------------------------------------------

data Value = VNumber Number | VArr [Value]

instance Show Value where
  show (VNumber (I32 n)) = show n
  show (VNumber (F32 n)) = show n
  show (VNumber (I64 n)) = show n
  show (VNumber (F64 n)) = show n
  show (VArr as) = "[" <> intercalate ", " (fmap show as) <> "]"

type Mem = Map Int Value

data GenState = GenState
  { nextCell :: Int
  , initialMem :: Mem
  , tick :: Mem -> Mem
  }

type SimM = R.ReaderT Mem (ST.State [Value])
type CircuitM = R.ReaderT (Map Ident (SimM Value)) (ST.State GenState)

pop :: SimM Value
pop = ST.get >>= \stack -> case stack of
  (h:t) -> ST.put t >> pure h
  [] -> error "pop: empty stack"

push :: Value -> SimM ()
push v = ST.modify (v:)

interpret :: Expr Type -> CircuitM (SimM Value)
interpret (EConst n) = pure (pure $ VNumber n)
interpret (EOp _ op a b) = do
  sima <- interpret a
  simb <- interpret b
  pure $ do
    a <- sima
    b <- simb
    case (op, a, b) of
      -- I32 operations
      (Add, VNumber (I32 a), VNumber (I32 b)) -> pure $ VNumber $ I32 (a + b)
      (Sub, VNumber (I32 a), VNumber (I32 b)) -> pure $ VNumber $ I32 (a - b)
      (Mul, VNumber (I32 a), VNumber (I32 b)) -> pure $ VNumber $ I32 (a * b)
      (Div, VNumber (I32 a), VNumber (I32 b)) -> pure $ VNumber $ I32 (a `div` b)
      (Mod, VNumber (I32 a), VNumber (I32 b)) -> pure $ VNumber $ I32 (a `mod` b)
      (Rem, VNumber (I32 a), VNumber (I32 b)) -> pure $ VNumber $ I32 (a `rem` b)
      (And, VNumber (I32 a), VNumber (I32 b)) -> pure $ VNumber $ I32 (a .&. b)
      (Or, VNumber (I32 a), VNumber (I32 b)) -> pure $ VNumber $ I32 (a .|. b)
      (Xor, VNumber (I32 a), VNumber (I32 b)) -> pure $ VNumber $ I32 (a `xor` b)
      (Shl, VNumber (I32 a), VNumber (I32 b)) -> pure $ VNumber $ I32 (a `shiftL` b)
      (Shr, VNumber (I32 a), VNumber (I32 b)) -> pure $ VNumber $ I32 (a `shiftR` b)
      (Rotl, VNumber (I32 a), VNumber (I32 b)) -> pure $ VNumber $ I32 (a `rotateL` b)
      (Rotr, VNumber (I32 a), VNumber (I32 b)) -> pure $ VNumber $ I32 (a `rotateR` b)
      (Eq, VNumber (I32 a), VNumber (I32 b)) -> pure $ VNumber $ I32 (if a == b then 1 else 0)
      (Ne, VNumber (I32 a), VNumber (I32 b)) -> pure $ VNumber $ I32 (if a /= b then 1 else 0)
      (Gt, VNumber (I32 a), VNumber (I32 b)) -> pure $ VNumber $ I32 (if a > b then 1 else 0)
      (Lt, VNumber (I32 a), VNumber (I32 b)) -> pure $ VNumber $ I32 (if a < b then 1 else 0)
      (GEt, VNumber (I32 a), VNumber (I32 b)) -> pure $ VNumber $ I32 (if a >= b then 1 else 0)
      (LEt, VNumber (I32 a), VNumber (I32 b)) -> pure $ VNumber $ I32 (if a <= b then 1 else 0)
      (Min, VNumber (I32 a), VNumber (I32 b)) -> pure $ VNumber $ I32 (min a b)
      (Max, VNumber (I32 a), VNumber (I32 b)) -> pure $ VNumber $ I32 (max a b)
      
      -- I64 operations
      (Add, VNumber (I64 a), VNumber (I64 b)) -> pure $ VNumber $ I64 (a + b)
      (Sub, VNumber (I64 a), VNumber (I64 b)) -> pure $ VNumber $ I64 (a - b)
      (Mul, VNumber (I64 a), VNumber (I64 b)) -> pure $ VNumber $ I64 (a * b)
      (Div, VNumber (I64 a), VNumber (I64 b)) -> pure $ VNumber $ I64 (a `div` b)
      (Mod, VNumber (I64 a), VNumber (I64 b)) -> pure $ VNumber $ I64 (a `mod` b)
      (Rem, VNumber (I64 a), VNumber (I64 b)) -> pure $ VNumber $ I64 (a `rem` b)
      (And, VNumber (I64 a), VNumber (I64 b)) -> pure $ VNumber $ I64 (a .&. b)
      (Or, VNumber (I64 a), VNumber (I64 b)) -> pure $ VNumber $ I64 (a .|. b)
      (Xor, VNumber (I64 a), VNumber (I64 b)) -> pure $ VNumber $ I64 (a `xor` b)
      (Shl, VNumber (I64 a), VNumber (I64 b)) -> pure $ VNumber $ I64 (a `shiftL` b)
      (Shr, VNumber (I64 a), VNumber (I64 b)) -> pure $ VNumber $ I64 (a `shiftR` b)
      (Rotl, VNumber (I64 a), VNumber (I64 b)) -> pure $ VNumber $ I64 (a `rotateL` b)
      (Rotr, VNumber (I64 a), VNumber (I64 b)) -> pure $ VNumber $ I64 (a `rotateR` b)
      (Eq, VNumber (I64 a), VNumber (I64 b)) -> pure $ VNumber $ I32 (if a == b then 1 else 0)
      (Ne, VNumber (I64 a), VNumber (I64 b)) -> pure $ VNumber $ I32 (if a /= b then 1 else 0)
      (Gt, VNumber (I64 a), VNumber (I64 b)) -> pure $ VNumber $ I32 (if a > b then 1 else 0)
      (Lt, VNumber (I64 a), VNumber (I64 b)) -> pure $ VNumber $ I32 (if a < b then 1 else 0)
      (GEt, VNumber (I64 a), VNumber (I64 b)) -> pure $ VNumber $ I32 (if a >= b then 1 else 0)
      (LEt, VNumber (I64 a), VNumber (I64 b)) -> pure $ VNumber $ I32 (if a <= b then 1 else 0)
      (Min, VNumber (I64 a), VNumber (I64 b)) -> pure $ VNumber $ I64 (min a b)
      (Max, VNumber (I64 a), VNumber (I64 b)) -> pure $ VNumber $ I64 (max a b)
      
      -- F32 operations
      (Add, VNumber (F32 a), VNumber (F32 b)) -> pure $ VNumber $ F32 (a + b)
      (Sub, VNumber (F32 a), VNumber (F32 b)) -> pure $ VNumber $ F32 (a - b)
      (Mul, VNumber (F32 a), VNumber (F32 b)) -> pure $ VNumber $ F32 (a * b)
      (Div, VNumber (F32 a), VNumber (F32 b)) -> pure $ VNumber $ F32 (a / b)
      (Eq, VNumber (F32 a), VNumber (F32 b)) -> pure $ VNumber $ I32 (if a == b then 1 else 0)
      (Ne, VNumber (F32 a), VNumber (F32 b)) -> pure $ VNumber $ I32 (if a /= b then 1 else 0)
      (Gt, VNumber (F32 a), VNumber (F32 b)) -> pure $ VNumber $ I32 (if a > b then 1 else 0)
      (Lt, VNumber (F32 a), VNumber (F32 b)) -> pure $ VNumber $ I32 (if a < b then 1 else 0)
      (GEt, VNumber (F32 a), VNumber (F32 b)) -> pure $ VNumber $ I32 (if a >= b then 1 else 0)
      (LEt, VNumber (F32 a), VNumber (F32 b)) -> pure $ VNumber $ I32 (if a <= b then 1 else 0)
      (Min, VNumber (F32 a), VNumber (F32 b)) -> pure $ VNumber $ F32 (min a b)
      (Max, VNumber (F32 a), VNumber (F32 b)) -> pure $ VNumber $ F32 (max a b)
      (CopySign, VNumber (F32 a), VNumber (F32 b)) -> pure $ VNumber $ F32 (copySign a b)
      
      -- F64 operations
      (Add, VNumber (F64 a), VNumber (F64 b)) -> pure $ VNumber $ F64 (a + b)
      (Sub, VNumber (F64 a), VNumber (F64 b)) -> pure $ VNumber $ F64 (a - b)
      (Mul, VNumber (F64 a), VNumber (F64 b)) -> pure $ VNumber $ F64 (a * b)
      (Div, VNumber (F64 a), VNumber (F64 b)) -> pure $ VNumber $ F64 (a / b)
      (Eq, VNumber (F64 a), VNumber (F64 b)) -> pure $ VNumber $ I32 (if a == b then 1 else 0)
      (Ne, VNumber (F64 a), VNumber (F64 b)) -> pure $ VNumber $ I32 (if a /= b then 1 else 0)
      (Gt, VNumber (F64 a), VNumber (F64 b)) -> pure $ VNumber $ I32 (if a > b then 1 else 0)
      (Lt, VNumber (F64 a), VNumber (F64 b)) -> pure $ VNumber $ I32 (if a < b then 1 else 0)
      (GEt, VNumber (F64 a), VNumber (F64 b)) -> pure $ VNumber $ I32 (if a >= b then 1 else 0)
      (LEt, VNumber (F64 a), VNumber (F64 b)) -> pure $ VNumber $ I32 (if a <= b then 1 else 0)
      (Min, VNumber (F64 a), VNumber (F64 b)) -> pure $ VNumber $ F64 (min a b)
      (Max, VNumber (F64 a), VNumber (F64 b)) -> pure $ VNumber $ F64 (max a b)
      (CopySign, VNumber (F64 a), VNumber (F64 b)) -> pure $ VNumber $ F64 (copySign a b)
      
      _ -> error $ "interpret EOp: unsupported operation: " ++ show (op, a, b)
interpret (EArr _ as) = do
  simas <- traverse interpret as
  pure $ do
    as <- sequence simas
    pure $ VArr as
interpret (EVar _ n) = do
  env <- R.ask
  case M.lookup n env of
    Just var -> pure var
    Nothing -> error $ "interpret: var not in scoope: " <> show n
interpret (EAbs _ params bindings body) = mdo
  simbindings <- fmap M.fromList $ sequence $ mconcat
    [ [ (p,) <$> pure pop | p <- params ]
    , [ fmap (n,) $ R.local (\env -> simbindings <> env) $ interpret bbody
      | (n, bbody) <- bindings
      ]
    ]
  R.local (\env -> simbindings <> env) $ interpret body
interpret (ESelect _ expr idx) = do
  simexpr <- interpret expr
  simidx <- interpret idx
  pure $ do
    e <- simexpr
    i <- simidx
    case (e, i) of
      (VArr as, VNumber (I32 i')) -> pure (as !! i')
      (VArr as, VNumber (I64 i')) -> pure (as !! i')
      (e', i') -> error $ "ESelect: " <> show e' <> ", " <> show i'
interpret (EApp _ f params) = do
  simargs <- traverse interpret params
  simf <- interpret f
  pure $ do
    sequence_ [ push =<< arg | arg <- simargs ]
    simf
interpret (ERec t delay param bindings body) = mdo
  nextCell <- ST.gets (.nextCell)
  ST.modify $ \st -> st { nextCell = st.nextCell + 2 }

  let delayBufferIdx = nextCell
  let delayIndexIdx = nextCell + 1

  let initialValue = alloc (TArr t (delay + 1))

  let delayLine offset = R.ask >>= \mem -> do
        let delayBuffer = lookupE "delayBuffer" mem delayBufferIdx
        let delayIdx = lookupE "delayIdx" mem delayIndexIdx
        case (delayBuffer, delayIdx) of
          (VArr ds, VNumber (I32 i)) -> pure (ds !! ((i - offset) `mod` delay))
          _ -> error "delayLine (this is a bug)"

  simbindings <- fmap M.fromList $ sequence $ mconcat
    [ [ pure (param, delayLine delay) ]
    , [ fmap (n,) $ R.local (\env -> simbindings <> env) $ interpret bbody
      | (n, bbody) <- bindings
      ]
    ]

  simbody <- R.local (\env -> simbindings <> env) $ interpret body

  ST.modify $ \st -> st
    { initialMem = M.fromList [(delayBufferIdx, initialValue), (delayIndexIdx, VNumber (I32 (delay - 1)))] <> st.initialMem
    , tick = \mem -> let
        mem' = st.tick mem
        nextValue = ST.evalState (R.runReaderT simbody mem') []

        delayBuffer = lookupE "delayBuffer: tick" mem' delayBufferIdx
        delayIndex = lookupE "delayIndex: tick" mem' delayIndexIdx

        in case (delayBuffer, delayIndex) of
          (VArr ds, VNumber (I32 i)) -> M.fromList
            [ (delayBufferIdx, VArr $ replace i nextValue ds)
            , (delayIndexIdx, VNumber (I32 ((i + 1) `mod` delay)))
            ]
            <> mem'
          _ -> error "delayLine (this is a bug)"
    }

  pure (delayLine 0)
  where
    replace i a as = take i as <> [a] <> drop (i + 1) as

    alloc (TNumber TI32) = VNumber (I32 0)
    alloc (TNumber TF32) = VNumber (F32 0)
    alloc (TNumber TI64) = VNumber (I64 0)
    alloc (TNumber TF64) = VNumber (F64 0)
    alloc (TArr t n) = VArr $ take n $ repeat (alloc t)
    alloc (TAbs _ _) = error "interpret: ERec: function in return type"

tinterpretToList :: Expr Type -> [Value]
tinterpretToList texpr = take 20 (go st.initialMem st.tick sim)
  where
    go mem tick sim = ST.evalState (R.runReaderT sim mem) []:go (tick mem) tick sim
    (sim, st) = ST.runState (R.runReaderT (interpret texpr) mempty) (GenState { nextCell = 0, initialMem = mempty, tick = id })

interpretToList :: Expr () -> [Value]
interpretToList expr = take 20 (go st.initialMem st.tick sim)
  where
    go mem tick sim = ST.evalState (R.runReaderT sim mem) []:go (tick mem) tick sim

    Right texpr = infer expr
    (sim, st) = ST.runState (R.runReaderT (interpret texpr) mempty) (GenState { nextCell = 0, initialMem = mempty, tick = id })

--------------------------------------------------------------------------------

es :: [(Ident, Expr ())]
es = 
  [ ("x", i32 5)
  , ("n", f32 5)
  , ("f", abs_ ["p" |: ti32] ([ti32] --> ti32) [] $ abs_ ["o" |: ti32 ] ti32 [] $ op Add (var "o") (var "p"))
  , ("z", app (app (var "f") [var "x"]) [app (var "rec") []])
  , ("rec", abs_ [] ti32 [] $ rec_ ti32 5 "cnt" [] (op Add (i32 1) (var "cnt")))
  ]

et :: Expr ()
et = abs_ [] ti32
  [ ("x", i32 666)
  , ("n", i32 777)
  , ("arr", arr [i32 0, i32 1, i32 3])
  , ("f", abs_ ["p" |: ti32] ([ti32] --> ti32) [] $ abs_ ["o" |: ti32 ] ti32 [] $ op Add (var "o") (var "p"))
  , ("z", app (app (var "f") [var "x"]) [sel (arr [i32 89, i32 99, i32 101]) (var "rec")])
  , ("rec", rec_ ti32 2 "cnt" [] (op Add (sel (var "arr") (i32 2)) (var "cnt")))
  ]
  (var "rec")

et2 = ERec (TNumber TI64) 1 (Ident "a") [(Ident "b",ERec (TNumber TF32) 2 (Ident "c") [] (EOp (TNumber TF32) Add (EVar (TNumber TF32) (Ident "c")) (EVar (TNumber TF32) (Ident "c"))))] (EOp (TNumber TI64) Sub (ERec (TNumber TI64) 4 (Ident "d") [(Ident "e",EAbs (TAbs [TNumber TI32,TNumber TI64] (TArr (TNumber TI64) 3)) [Ident "f",Ident "g"] [] (EArr (TArr (TNumber TI64) 3) [EConst (I64 0),EConst (I64 0),EConst (I64 0)]))] (EOp (TNumber TI64) Add (EOp (TNumber TI64) Sub (EVar (TNumber TI64) (Ident "d")) (EConst (I64 2))) (EConst (I64 0)))) (EVar (TNumber TI64) (Ident "a")))
et3 = ERec (TArr (TNumber TI64) 4) 1 (Ident "x402") [(Ident "a809",EAbs (TAbs [] (TNumber TF64)) [] [] (EConst (F64 0.0))),(Ident "b267",EAbs (TAbs [TAbs [TNumber TF32,TNumber TI64] (TNumber TI64),TNumber TI64,TAbs [TNumber TI32] (TNumber TF32)] (TAbs [TNumber TI32] (TNumber TI64))) [Ident "x18",Ident "f549",Ident "g533"] [(Ident "g998",EConst (I64 0)),(Ident "b474",EArr (TArr (TAbs [TNumber TI32] (TNumber TF64)) 5) [EAbs (TAbs [TNumber TI32] (TNumber TF64)) [Ident "b901"] [(Ident "a680",EConst (I64 0)),(Ident "c189",EArr (TArr (TNumber TI32) 2) [EConst (I32 0),EConst (I32 0)])] (EConst (F64 0.0)),EAbs (TAbs [TNumber TI32] (TNumber TF64)) [Ident "f596"] [(Ident "a956",EConst (F32 0.48784024)),(Ident "b125",EVar (TNumber TI64) (Ident "g998"))] (EConst (F64 0.0)),EAbs (TAbs [TNumber TI32] (TNumber TF64)) [Ident "g339"] [(Ident "c769",EArr (TArr (TNumber TI64) 5) [EConst (I64 0),EConst (I64 0),EConst (I64 0),EConst (I64 0),EConst (I64 0)]),(Ident "y983",EConst (I64 0)),(Ident "z339",EConst (F32 0.0))] (EConst (F64 0.0)),EAbs (TAbs [TNumber TI32] (TNumber TF64)) [Ident "y58"] [(Ident "c980",EConst (F64 0.0)),(Ident "z285",EConst (I64 0))] (EVar (TNumber TF64) (Ident "c980")),EAbs (TAbs [TNumber TI32] (TNumber TF64)) [Ident "x724"] [(Ident "x898",EConst (I32 0))] (EConst (F64 0.0))]),(Ident "z782",EConst (I32 0))] (EAbs (TAbs [TNumber TI32] (TNumber TI64)) [Ident "b142"] [] (EVar (TNumber TI64) (Ident "f549"))))] (EArr (TArr (TNumber TI64) 4) [ESelect (TNumber TI64) (EVar (TArr (TNumber TI64) 4) (Ident "x402")) (EConst (I64 1)),ESelect (TNumber TI64) (EVar (TArr (TNumber TI64) 4) (Ident "x402")) (EConst (I32 3)),ESelect (TNumber TI64) (EVar (TArr (TNumber TI64) 4) (Ident "x402")) (EConst (I32 3)),ESelect (TNumber TI64) (EVar (TArr (TNumber TI64) 4) (Ident "x402")) (EConst (I32 0))])
et4 = ERec (TArr (TNumber TI64) 3) 1 (Ident "z359") [] (ESelect (TNumber TI64) (EVar (TArr (TNumber TI64) 3) (Ident "z359")) (EConst (I64 1)))
et6 = ERec (TNumber TI32) 5 (Ident "b845") [] (EOp (TNumber TI32) Add (EOp (TNumber TI32) Sub (EVar (TNumber TI32) (Ident "b845")) (EApp (TNumber TI32) (EAbs (TAbs [TArr (TArr (TNumber TI64) 3) 3,TNumber TF64,TNumber TF64] (TNumber TI32)) [Ident "y921",Ident "c86",Ident "y781"] [(Ident "b287",EConst (F64 0.0))] (EVar (TNumber TI32) (Ident "b845"))) [EArr (TArr (TArr (TNumber TI64) 3) 3) [EArr (TArr (TNumber TI64) 3) [EConst (I64 0),EConst (I64 0),EConst (I64 0)],EArr (TArr (TNumber TI64) 3) [EConst (I64 0),EConst (I64 0),EConst (I64 0)],EArr (TArr (TNumber TI64) 3) [EConst (I64 0),EConst (I64 0),EConst (I64 0)]],EConst (F64 (-1.0)),EApp (TNumber TF64) (EAbs (TAbs [] (TNumber TF64)) [] [(Ident "a365",EConst (I32 0)),(Ident "b194",EConst (I64 0)),(Ident "f861",EConst (F64 0.0))] (EConst (F64 0.0))) []])) (EOp (TNumber TI32) Add (EApp (TNumber TI32) (EAbs (TAbs [TNumber TF64] (TNumber TI32)) [Ident "c326"] [(Ident "a957",EArr (TArr (TNumber TF64) 4) [EConst (F64 0.0),EVar (TNumber TF64) (Ident "c326"),EConst (F64 0.0),EConst (F64 0.25970278568437655)]),(Ident "g306",EArr (TArr (TArr (TNumber TF32) 4) 1) [EArr (TArr (TNumber TF32) 4) [EConst (F32 0.0),EConst (F32 0.0),EConst (F32 0.0),EConst (F32 0.0)]])] (EConst (I32 0))) [EConst (F64 0.0)]) (ESelect (TNumber TI32) (EArr (TArr (TNumber TI32) 5) [EConst (I32 0),EConst (I32 0),EConst (I32 0),EConst (I32 0),EVar (TNumber TI32) (Ident "b845")]) (EConst (I32 1)))))

t2 = do
  putStrLn "ALLOCS"
  print ir.globalAllocations
  putStrLn "---"

  putStrLn "TICK"
  print ir.tickFunc.allocations
  putStrLn $ showBlock ir.tickFunc.instructions
  putStrLn "---"

  sequence_
    [ do
        print fr
        putStrLn "---"
        putStrLn $ showBlock f.instructions
        putStrLn ""
        print f.allocations
        putStrLn ""
    | (FuncRef fr, f) <- M.toList ir.funcMap
    ]
  where
    Right et' = infer et
    ces = toCExpr et'
    (CAbs _ fr, funcRefMap, genv) = compile3 ces
    ir = toplevel genv.globals funcRefMap fr

t3 = fmap compile2 ces
  where
    es' = inferMany es
    ces = fmap (M.fromList . fmap (fmap toCExpr)) es'

t4 = fmap compile3 ces
  where
    et' = infer et
    ces = fmap toCExpr et'
