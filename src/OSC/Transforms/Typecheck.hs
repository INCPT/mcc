{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module OSC.Transforms.Typecheck where

import Control.Monad (when)
import Control.Monad.Trans.Class (lift)
import qualified Control.Monad.Reader as R
import qualified Control.Monad.Except as E
import qualified Control.Monad.Writer as W

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Graph as G

import OSC.Expr.Functors
import OSC.Expr.Plate
import OSC.Expr.TH
import OSC.Expr.Comp (Number (..), Ident (..), TNumber (..), Type (..), Op (..))
import qualified OSC.Expr.Comp as C
import OSC.Expr.Base
import qualified OSC.Expr.Base as B

--------------------------------------------------------------------------------

data TypeError pos
  = BinOpTypeMismatch pos pos Op Type Type
  | BinOpInvalidTypes pos pos Op Type Type
  | EmptyArray pos
  | ArrayElementTypeMismatch pos [Type]
  | UnknownBinding pos Ident
  | FunctionReturnTypeMismatch pos Type Type
  | ArgumentCountMismatch pos Int Int
  | ArgumentTypeMismatch pos Int Type Type
  | NotAnArray pos Type
  | InvalidIndexType pos Type
  | RecDelayNotPositive pos Int
  | RecTypeContainsFunction pos Type
  | RecReturnTypeMismatch pos Type Type
  | DuplicateBindings pos [Ident]
  | CyclicDependency pos [G.Tree G.Vertex]
  | NotAFunction pos Type
  deriving Show

type ExpA ann = Ann ann Expr
type TypecheckM pos = R.ReaderT (Map Ident Type) (E.Except (TypeError pos))

-- Helper functions
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

checkDuplicates :: pos -> [(Ident, a)] -> TypecheckM pos ()
checkDuplicates pos bindings = do
  let counts = M.fromListWith (+) ((, 1 :: Int) <$> fmap fst bindings)
  let dups = [ n | (n, x) <- M.toList counts, x > 1 ]
  case dups of
    [] -> pure ()
    _ -> E.throwError $ DuplicateBindings pos dups

checkCycles :: Show ann => pos -> [(Ident, ExpA ann)] -> TypecheckM pos [(Ident, ExpA ann)]
checkCycles pos bindings = do
  let nodeEdges expr = S.fromList [ {- (\x -> trace ("VAR :" <> show x) x) $ -} n | Ann (_, Var n) <- universe (snd . unAnn) expr ]
  case topsort nodeEdges bindings of
    Left scc -> E.throwError $ CyclicDependency pos scc
    Right sorted -> pure sorted

typeContainsLam :: Type -> Bool
typeContainsLam (TNumber _) = False
typeContainsLam (TArr t _) = typeContainsLam t
typeContainsLam (TLam _ _) = True

-- Typecheck bindings with dependency ordering
typecheckBindings :: Show pos => pos -> [(Ident, ExpA pos)] -> TypecheckM pos [(Ident, ExpA (pos, Type))]
typecheckBindings pos bindings = do
  -- Check for duplicates
  checkDuplicates pos bindings
  
  -- Check for cycles
  bindings' <- {- fmap (\x -> trace ("SORTED BINDINGS: " <> show x) x) $ -} checkCycles pos bindings
  go bindings'
  where
    go [] = pure []
    go ((n, expr):bs) = do
      expr' <- typecheck expr
      let exprType = snd . fst . unAnn $ expr'
      bs' <- R.local (M.insert n exprType) $ go bs
      return $ (n, expr'):bs'

typecheck :: Show pos => ExpA pos -> TypecheckM pos (ExpA (pos, Type))
typecheck expr = case unAnn expr of
  (pos, Const n) -> 
    pure $ Ann ((pos, C.numberType n), Const n)
  
  (pos, Op op a b) -> do
    a' <- typecheck a
    b' <- typecheck b
    
    let apos = fst . fst . unAnn $ a'
    let bpos = fst . fst . unAnn $ b'
    let at = snd . fst . unAnn $ a'
    let bt = snd . fst . unAnn $ b'
    
    case (op, at, bt) of
      -- Arithmetic operations: return same type as operands
      (Add, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (Sub, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (Mul, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (Div, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (Mod, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (Rem, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (Min, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (Max, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (CopySign, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber t), Op op a' b')
      
      -- Bitwise operations: integer types only
      (And, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (Or, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (Xor, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (Shl, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (Shr, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (Rotl, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (Rotr, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> pure $ Ann ((pos, TNumber t), Op op a' b')
      
      -- Comparison operations: return I32 (boolean)
      (Eq, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber TI32), Op op a' b')
      (Ne, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber TI32), Op op a' b')
      (Gt, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber TI32), Op op a' b')
      (Lt, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber TI32), Op op a' b')
      (GEt, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber TI32), Op op a' b')
      (LEt, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber TI32), Op op a' b')
      
      -- Type mismatch error
      (_, TNumber t, TNumber u) | t /= u -> E.throwError $ BinOpTypeMismatch apos bpos op at bt
      _ -> E.throwError $ BinOpInvalidTypes apos bpos op at bt
  
  (pos, Arr []) -> E.throwError $ EmptyArray pos
  (pos, Arr (a:as)) -> do
    a' <- typecheck a
    as' <- traverse typecheck as
    let at = snd . fst . unAnn $ a'
    let types = fmap (snd . fst . unAnn) as'
    if all (== at) types
      then pure $ Ann ((pos, TArr at (length as + 1)), Arr (a':as'))
      else E.throwError $ ArrayElementTypeMismatch pos (at:types)
  
  (pos, Var n) -> do
    env <- R.ask
    case M.lookup n env of
      Just t -> pure $ Ann ((pos, t), Var n)
      Nothing -> E.throwError $ UnknownBinding pos n
  
  (pos, Lam t params bindings body) -> do
    -- Check for duplicate parameters  
    checkDuplicates pos [(p, ()) | p <- params]
    checkDuplicates pos bindings
    
    -- Extract parameter types and return type from the function type
    case t of
      TLam paramTypes retType -> do
        -- Check parameter count matches
        when (length params /= length paramTypes) $
          E.throwError $ ArgumentCountMismatch pos (length paramTypes) (length params)
        
        -- Build parameter environment
        let paramsEnv = M.fromList (zip params paramTypes)
        
        -- Typecheck bindings in the context of parameters
        bindings' <- R.local (paramsEnv <>) $ typecheckBindings pos bindings
        
        -- Build full environment for body (params + bindings)
        let bindingsEnv = M.fromList [(n, snd . fst . unAnn $ e) | (n, e) <- bindings']
        body' <- R.local ((bindingsEnv <> paramsEnv) <>) $ typecheck body
        
        let bodyType = snd . fst . unAnn $ body'
        
        -- Check return type matches
        when (bodyType /= retType) $
          E.throwError $ FunctionReturnTypeMismatch pos retType bodyType
        
        pure $ Ann ((pos, t), Lam t params bindings' body')
      
      _ -> E.throwError $ NotAFunction pos t
  
  (pos, App func args) -> do
    func' <- typecheck func
    args' <- traverse typecheck args
    
    let funcType = snd . fst . unAnn $ func'
    let argTypes = fmap (snd . fst . unAnn) args'
    
    case funcType of
      TLam paramTypes retType -> do
        -- Check argument count
        when (length paramTypes /= length args) $
          E.throwError $ ArgumentCountMismatch pos (length paramTypes) (length args)
        
        -- Check each argument type
        sequence_
          [ when (pt /= at) $
              E.throwError $ ArgumentTypeMismatch (fst . fst . unAnn $ arg) i pt at
          | (i, (pt, (at, arg))) <- zip [0..] $ zip paramTypes $ zip argTypes args'
          ]
        
        pure $ Ann ((pos, retType), App func' args')
      _ -> E.throwError $ NotAFunction (fst . fst . unAnn $ func') funcType
  
  (pos, Select sel idx) -> do
    sel' <- typecheck sel
    idx' <- typecheck idx
    
    let selType = snd . fst . unAnn $ sel'
    let idxType = snd . fst . unAnn $ idx'
    
    case selType of
      TArr elemType _ -> do
        case idxType of
          TNumber TI32 -> pure $ Ann ((pos, elemType), Select sel' idx')
          TNumber TI64 -> pure $ Ann ((pos, elemType), Select sel' idx')
          _ -> E.throwError $ InvalidIndexType (fst . fst . unAnn $ idx') idxType
      _ -> E.throwError $ NotAnArray (fst . fst . unAnn $ sel') selType
  
  (pos, Rec t delay param bindings body) -> do
    -- Check for duplicates
    checkDuplicates pos bindings
    
    -- Check that the type doesn't contain functions
    when (typeContainsLam t) $
      E.throwError $ RecTypeContainsFunction pos t
    
    -- Build parameter environment (the recursive parameter has the delay type)
    let paramsEnv = M.singleton param t
    
    -- Typecheck bindings in the context of the recursive parameter
    bindings' <- R.local (paramsEnv <>) $ typecheckBindings pos bindings
    
    -- Build full environment for body (param + bindings)
    let bindingsEnv = M.fromList [(n, snd . fst . unAnn $ e) | (n, e) <- bindings']
    body' <- R.local ((bindingsEnv <> paramsEnv) <>) $ typecheck body
    
    let bodyType = snd . fst . unAnn $ body'
    
    -- Check return type matches the delay type
    when (bodyType /= t) $
      E.throwError $ RecReturnTypeMismatch pos t bodyType
    
    pure $ Ann ((pos, t), Rec t delay param bindings' body')

--------------------------------------------------------------------------------

infer :: Show pos => ExpA pos -> Either (TypeError pos) (Ann Type Expr)
infer = fmap (hoistAnn snd) . E.runExcept . flip R.runReaderT mempty . typecheck

dbgInfer :: Show pos => ExpA pos -> Ann Type Expr
dbgInfer expr = case fmap (hoistAnn snd) $ E.runExcept $ flip R.runReaderT mempty $ typecheck expr of
  Right a -> a
  Left e -> error $ show e

--------------------------------------------------------------------------------

class RecursiveWrapper f where
  type WrapContext f :: * -> *
  runwrap :: f expr -> WrapContext f (expr (f expr))
  rwrap :: (expr (f expr) -> expr (f expr)) -> f expr -> f expr

mjoin :: Monad m => m (m a) -> m a
mjoin = undefined

transformGeneric
  :: (RecursiveWrapper f, Traversable expr, Monad m, Monad (WrapContext f))
  => (expr (f expr) -> m (expr (f expr)))  -- transformer
  -> f expr
  -> WrapContext f (m (f expr))
transformGeneric trans wrapped = do
  expr <- runwrap wrapped  -- unwrap in WrapContext monad
  return $ do
    expr' <- trans expr  -- transform in m monad
    expr'' <- traverse (\child -> mjoin $ transformGeneric trans child) expr'  -- recurse
    return $ rwrap (Prelude.const expr'') wrapped

-- For your capture analysis:
markCapturedBindingsGeneric
  :: (RecursiveWrapper f, Monad m)
  => f Expr
  -> CaptureM m (f Expr)
markCapturedBindingsGeneric = transformGeneric $ \expr -> case expr of
  Var n -> do
    env <- R.ask
    when (S.member n env) $ W.tell (S.singleton n)
    return (Var n)

  Lam t params bindings body -> do
    env <- R.ask
    let paramsEnv = S.fromList params

    -- Process bindings
    bindings' <- forM bindings $ \(n, e) ->
      (n,) <$> R.local (paramsEnv <>) (markCapturedBindingsGeneric e)

    -- Process body and capture free vars
    (body', captured) <- W.listen $
      R.local (paramsEnv <>) (markCapturedBindingsGeneric body)

    -- Propagate captures excluding params
    W.tell (captured S.\\ paramsEnv)

    return $ Lam t params bindings' body'

  e -> return e  -- transformGeneric handles recursion

--------------------------------------------------------------------------------

type CaptureM m = R.ReaderT (Set Ident) (W.WriterT (Set Ident) m)

transformM2
  :: (Empty (f' Expr) -> m (Expr (f' Expr)))
  -> ((Expr (f Expr) -> m (Expr (f' Expr))) -> Expr (f Expr) -> m (Expr (f' Expr)))
  -> Expr (f Expr) -> m (Expr (f' Expr))
transformM2 = undefined

markCapturedBindings'' :: Monad m => Expr (Ann Type Expr) -> CaptureM m (Expr (Ann Type Expr))
markCapturedBindings'' = transformM2 undefined $ \fdown expr -> case expr of
  Var n -> R.ask >>= \env -> (if S.member n env then W.tell (S.singleton n) else pure ()) >> pure (Var n)
  Lam _ params _ body -> do
    env <- R.ask
    let paramsEnv = S.fromList params
    
    -- TODO: bindings

    -- error here we'd need to unwrap
    -- body'' <- fdown body
    -- (body', captured) <- W.runWriterT $ R.runReaderT (markCapturedBindings'' body) (paramsEnv <> env)

    -- W.tell (captured S.\\ paramsEnv)
    -- -- and then wrap again here
    -- pure $ Lam undefined params undefined body'
    undefined
  e -> fdown e

markCapturedBindingsGen :: R.MonadReader (Set Ident) m => W.MonadWriter (Set Ident) m => (f Expr -> m (Expr (f Expr))) -> (Expr (f Expr) -> m (f Expr)) -> f Expr -> m (f Expr)
markCapturedBindingsGen unwrap wrap expr = unwrap expr >>= \expr -> case expr of
  Var n -> R.ask >>= \env -> (if S.member n env then W.tell (S.singleton n) else pure ()) >> wrap (Var n)
  Lam _ params _ body -> do
    env <- R.ask
    let paramsEnv = S.fromList params

    (body', captured) <- W.runWriterT $ R.runReaderT (markCapturedBindingsGen (fmap (lift . lift) unwrap) (fmap (lift . lift) wrap) body) (paramsEnv <> env)

    W.tell (captured S.\\ paramsEnv)
    wrap $ Lam undefined params undefined body'
  e -> transformM unwrap (\e -> markCapturedBindingsGen unwrap wrap =<< wrap e) =<< wrap e

flowAnn :: (Ann ann f -> f (Ann ann f) -> m (Either (f (Ann ann f)) (Ann ann f))) -> Ann ann f -> m (Ann ann f)
flowAnn = undefined

markCapturedBindingsSpecific :: Monad m => ExpA Type -> CaptureM m (ExpA Type)
markCapturedBindingsSpecific = flowAnn $ \expa@(Ann (t, _)) exp -> case exp of
  Var n -> R.ask >>= \env -> (if S.member n env then W.tell (S.singleton n) else pure ()) >> pure (Left $ Var n)
  Lam _ params _ body -> do
    env <- R.ask
    let paramsEnv = S.fromList params
    
    -- TODO: bindings

    (body', captured) <- W.runWriterT $ R.runReaderT (markCapturedBindingsSpecific body) (paramsEnv <> env)

    W.tell (captured S.\\ paramsEnv)
    pure $ Left $ Lam undefined params undefined body'
  _ -> fmap Right $ transformM (pure . snd . unAnn) (markCapturedBindingsSpecific . (\f -> Ann (t, f))) expa

--------------------------------------------------------------------------------

e1 :: Ann () Expr
e1 = select (arr [(op Add (cnst $ C.I32 4) (cnst $ C.I32 8))]) (cnst $ C.I32 0)
  where
    cnst = B.const

e2 :: ExpA ()
e2 = Ann {unAnn = ((),Lam (TLam [] (TNumber TF32)) [] [(Ident "g756",Ann {unAnn = ((),Rec (TNumber TI64) 2 (Ident "b500") [(Ident "f453",Ann {unAnn = ((),App (Ann {unAnn = ((),Lam (TLam [TNumber TI64,TArr (TNumber TI32) 3] (TArr (TNumber TI32) 1)) [Ident "c130",Ident "f982"] [(Ident "b182",Ann {unAnn = ((),Const (F64 0.5030272493895455))}),(Ident "a179",Ann {unAnn = ((),Const (I32 0))}),(Ident "b8",Ann {unAnn = ((),Const (F64 (-1.0)))})] (Ann {unAnn = ((),Arr [Ann {unAnn = ((),Var (Ident "a179"))}])}))}) [Ann {unAnn = ((),Const (I64 1))},Ann {unAnn = ((),Arr [Ann {unAnn = ((),Const (I32 1))},Ann {unAnn = ((),Const (I32 (-1)))},Ann {unAnn = ((),Const (I32 (-1)))}])}])}),(Ident "y862",Ann {unAnn = ((),Const (F64 0.7922093797675532))}),(Ident "y851",Ann {unAnn = ((),Lam (TLam [] (TNumber TF64)) [] [(Ident "x699",Ann {unAnn = ((),Var (Ident "y862"))}),(Ident "g666",Ann {unAnn = ((),Const (F32 (-1.0)))})] (Ann {unAnn = ((),Var (Ident "x699"))}))})] (Ann {unAnn = ((),Op Add (Ann {unAnn = ((),Op Sub (Ann {unAnn = ((),Var (Ident "b500"))}) (Ann {unAnn = ((),Const (I64 1))}))}) (Ann {unAnn = ((),Const (I64 (-1)))}))}))})] (Ann {unAnn = ((),Const (F32 1.5))}))}

e3 = Ann {unAnn = ((),Lam (TLam [] (TNumber TF32)) [] [(Ident "x568",Ann {unAnn = ((),Const (F32 (-1.0)))}),(Ident "f477",Ann {unAnn = ((),Var (Ident "x568"))}),(Ident "a193",Ann {unAnn = ((),Const (F64 0.9879229879464689))})] (Ann {unAnn = ((),Const (F32 (-1.0)))}))}
