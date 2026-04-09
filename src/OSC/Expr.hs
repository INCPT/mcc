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

import Data.Generics.Uniplate.Data (universe)

import qualified Data.Graph as G
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import OSC.Ctx
import OSC.Call

newtype TypeError = TypeError String
  deriving Show

type GenM = E.ExceptT TypeError (R.Reader (Map Ident Type))

topsort :: Ord node => (a -> Set node) -> [(node, a)] -> Either [G.Tree G.Vertex] [(node, a)]
topsort nodeEdges nodes
  | hasCycles = Left (G.scc graph)
  | otherwise = Right [ (n, nodesMap M.! n) | v <- reverse (G.topSort graph), let (_, n, _) = nodeFromVertex v ]
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
  
  case exprType sel' of
    TNumber TI32 -> pure ()
    TNumber TI64 -> pure ()
    t -> E.throwError $ TypeError $ "typecheck: selection index not an integer: " <> show t
  
  pure $ ESelect t expr' sel'

typecheck (ERec t delay param bindings body) = do
  let paramsEnv = M.singleton param t

  bindings' <- R.local (\env -> paramsEnv <> env) $ typecheckBindings bindings
  body' <- R.local (\env -> M.fromList (fmap (fmap exprType) bindings') <> paramsEnv <> env) $ typecheck body
  
  when (typeContainsAbs t) $ E.throwError $ TypeError $ "typecheck: return type contains functions: " <> show t

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
  deriving Show

type Mem = Map Int Value

data GenState = GenState
  { nextCell :: Int
  , initialMem :: Mem
  , tick :: Mem -> Mem
  }

type SimM = R.Reader Mem Value
type CircuitM = R.ReaderT (Map Ident SimM) (ST.State GenState)

interpret :: [SimM] -> Expr Type -> CircuitM SimM
interpret _ (EConst n) = pure (pure $ VNumber n)
interpret _ (EOp _ op a b) = do
  sima <- interpret [] a
  simb <- interpret [] b
  pure $ do
    a <- sima
    b <- simb
    case (op, a, b) of
      (Add, VNumber (I32 a), VNumber (I32 b)) -> pure $ VNumber $ I32 (a + b)
      _ -> undefined
interpret _ (EArr _ as) = do
  simas <- traverse (interpret []) as
  pure $ do
    as <- sequence simas
    pure $ VArr as
interpret _ (EVar _ n) = do
  env <- R.ask
  pure (env M.! n) 
interpret args (EAbs _ params bindings body) = mdo
  simbindings <- fmap M.fromList $ sequence $ mconcat
    [ fmap pure (zip params args)
    , [ fmap (n,) $ R.local (\env -> simbindings <> env) $ interpret [] bbody
      | (n, bbody) <- bindings
      ]
    ]
  simbody <- R.local (\env -> simbindings <> env) $ interpret [] body
  pure simbody
interpret _ (ESelect _ expr idx) = do
  simexpr <- interpret [] expr
  simidx <- interpret [] idx
  pure $ do
    e <- simexpr
    i <- simidx
    case (e, i) of
      (VArr as, VNumber (I32 i')) -> pure (as !! i')
      (VArr as, VNumber (I64 i')) -> pure (as !! i')
      (e', i') -> error $ "ESelect: " <> show e' <> ", " <> show i'
interpret _ (EApp _ f params) = do
  simparams <- traverse (interpret []) params
  simf <- interpret simparams f
  pure simf
interpret _ (ERec t delay param bindings body) = mdo
  st <- ST.get

  let delayBufferIdx = st.nextCell
  let delayIndexIdx = st.nextCell + 1

  let initialValue = alloc (TArr t delay)

  let delayLine offset = R.ask >>= \mem -> do
        let delayBuffer = mem M.! delayBufferIdx
        let delayIdx = mem M.! delayIndexIdx
        case (delayBuffer, delayIdx) of
          (VArr ds, VNumber (I32 i)) -> pure (ds !! ((i - offset) `mod` delay))
          _ -> error "delayLine (this is a bug)"

  simbindings <- fmap M.fromList $ sequence $ mconcat
    [ [ pure (param, delayLine 1) ]
    , [ fmap (n,) $ R.local (\env -> simbindings <> env) $ interpret [] bbody
      | (n, bbody) <- bindings
      ]
    ]

  simbody <- R.local (\env -> simbindings <> env) $ interpret [] body

  ST.put $ st
    { nextCell = st.nextCell + 2
    , initialMem = M.fromList [(delayBufferIdx, initialValue), (delayIndexIdx, VNumber (I32 0))] <> st.initialMem
    , tick = \mem -> let
        mem' = st.tick mem
        nextValue = R.runReader simbody mem'

        delayBuffer = mem' M.! delayBufferIdx
        delayIndex = mem' M.! delayIndexIdx

        in case (delayBuffer, delayIndex) of
          (VArr ds, VNumber (I32 i)) -> M.fromList
            [ (delayBufferIdx, VArr $ replace i nextValue ds)
            , (delayIndexIdx, VNumber (I32 ((i + 1) `mod` delay)))
            ]
            <> mem'
          _ -> error "delayLine (this is a bug)"
    }

  pure (delayLine delay)
  where
    replace i a as = take i as <> [a] <> drop (i + 1) as

    alloc (TNumber TI32) = VNumber (I32 0)
    alloc (TNumber TF32) = VNumber (F32 0)
    alloc (TNumber TI64) = VNumber (I64 0)
    alloc (TNumber TF64) = VNumber (F64 0)
    alloc (TArr t n) = VArr $ take n $ repeat (alloc t)
    alloc (TAbs _ _) = error "interpret: ERec: function in return type"

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
  , ("arr", arr [i32 0, i32 1, i32 2])
  , ("f", abs_ ["p" |: ti32] ([ti32] --> ti32) [] $ abs_ ["o" |: ti32 ] ti32 [] $ op Add (var "o") (var "p"))
  , ("z", app (app (var "f") [var "x"]) [sel (arr [i32 89, i32 99, i32 101]) (var "rec")])
  , ("rec", rec_ ti32 5 "cnt" [] (op Add (sel (var "arr") (i32 2)) (var "cnt")))
  ]
  (var "rec")

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

i1 = do
  print $ take 10 (go st.initialMem st.tick sim)
  where
    go mem tick sim = R.runReader sim mem:go (tick mem) tick sim

    Right et' = infer et
    (sim, st) = ST.runState (R.runReaderT (interpret [] et') mempty) (GenState { nextCell = 0, initialMem = mempty, tick = id })