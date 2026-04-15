{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module OSC.Transforms.Typecheck where

import Control.Monad (when)
import Control.Monad.Trans.Class (lift)
import qualified Control.Monad.Reader as R
import qualified Control.Monad.Except as E

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Graph as G
import Data.List (find)
import Data.Generics.Uniplate.Data (universe)

import OSC.Expr.Functors
import OSC.Expr.TH
import OSC.Expr.Base (TNumber (..), Type (..), Op (..))
import qualified OSC.Expr.Base as B

-- Note: B.Lam and B.Rec contain type information in the original Expr
-- The Lam has: Lam [Ident] [(Ident, exp)] exp
-- The Rec has: Rec Ident [(Ident, exp)] exp
-- But EAbs has: EAbs Type [Ident] [(Ident, Expr t)] (Expr t)
-- And ERec has: ERec Type Int Ident [(Ident, Expr t)] (Expr t)
-- We need to handle the type annotation separately

$(makeSum "" "Exp" [''B.Exp, ''B.Lam, ''B.Select, ''B.Rec])
$(makeBiPlateInstance "" ''Exp "" ''Exp "" ''Empty)

--------------------------------------------------------------------------------

data TypeError pos
  = BinOpTypeMismatch pos pos Op Type Type
  | BinOpInvalidTypes pos pos Op Type Type
  | EmptyArray pos
  | ArrayElementTypeMismatch pos [Type]
  | UnknownBinding pos B.Ident
  | FunctionReturnTypeMismatch pos Type Type
  | ArgumentCountMismatch pos Int Int
  | ArgumentTypeMismatch pos Int Type Type
  | NotAnArray pos Type
  | InvalidIndexType pos Type
  | RecDelayNotPositive pos Int
  | RecTypeContainsFunction pos Type
  | RecReturnTypeMismatch pos Type Type
  | DuplicateBindings pos [B.Ident]
  | CyclicDependency pos [G.Tree G.Vertex]
  | NotAFunction pos Type
  deriving Show

type ExpA ann = Ann ann Exp
type TypecheckM pos = R.ReaderT (Map B.Ident Type) (E.Except (TypeError pos))

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

checkDuplicates :: pos -> [(B.Ident, a)] -> TypecheckM pos ()
checkDuplicates pos bindings = do
  let counts = M.fromListWith (+) ((, 1 :: Int) <$> fmap fst bindings)
  let dups = [ n | (n, x) <- M.toList counts, x > 1 ]
  case dups of
    [] -> pure ()
    _ -> E.throwError $ DuplicateBindings pos dups

checkCycles :: pos -> [(B.Ident, ExpA (pos, Type))] -> TypecheckM pos [(B.Ident, ExpA (pos, Type))]
checkCycles pos bindings = do
  undefined
  -- let nodeEdges expr = S.fromList [ n | Ann ((_, _), Var n) <- universe expr ]
  -- case topsort nodeEdges bindings of
  --   Left scc -> E.throwError $ CyclicDependency pos scc
  --   Right sorted -> pure sorted

typeContainsAbs :: Type -> Bool
typeContainsAbs (TNumber _) = False
typeContainsAbs (TArr t _) = typeContainsAbs t
typeContainsAbs (TAbs _ _) = True

-- Typecheck bindings with dependency ordering
typecheckBindings :: pos -> [(B.Ident, ExpA pos)] -> TypecheckM pos [(B.Ident, ExpA (pos, Type))]
typecheckBindings pos bindings = do
  -- Check for duplicates
  checkDuplicates pos bindings
  
  -- Check for cycles
  bindings' <- checkCycles pos =<< go bindings
  pure bindings'
  where
    go [] = pure []
    go ((n, expr):bs) = do
      expr' <- typecheck expr
      let exprType = snd . fst . unAnn $ expr'
      bs' <- R.local (M.insert n exprType) $ (go bs)
      return $ (n, expr'):bs'

typecheck :: ExpA pos -> TypecheckM pos (ExpA (pos, Type))
typecheck expr = case unAnn expr of
  (pos, Const n) -> 
    pure $ Ann ((pos, B.numberType n), Const n)
  
  (pos, Op op a b) -> do
    a' <- typecheck a
    b' <- typecheck b
    
    let apos = fst . fst . unAnn $ a'
    let bpos = fst . fst . unAnn $ b'
    let at = snd . fst . unAnn $ a'
    let bt = snd . fst . unAnn $ b'
    
    case (op, at, bt) of
      -- Arithmetic operations: return same type as operands
      (B.Add, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (B.Sub, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (B.Mul, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (B.Div, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (B.Mod, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (B.Rem, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (B.Min, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (B.Max, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (B.CopySign, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber t), Op op a' b')
      
      -- Bitwise operations: integer types only
      (B.And, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (B.Or, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (B.Xor, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (B.Shl, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (B.Shr, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (B.Rotl, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> pure $ Ann ((pos, TNumber t), Op op a' b')
      (B.Rotr, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> pure $ Ann ((pos, TNumber t), Op op a' b')
      
      -- Comparison operations: return I32 (boolean)
      (B.Eq, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber TI32), Op op a' b')
      (B.Ne, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber TI32), Op op a' b')
      (B.Gt, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber TI32), Op op a' b')
      (B.Lt, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber TI32), Op op a' b')
      (B.GEt, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber TI32), Op op a' b')
      (B.LEt, TNumber t, TNumber u) | t == u -> pure $ Ann ((pos, TNumber TI32), Op op a' b')
      
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
      TAbs paramTypes retType -> do
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
      TAbs paramTypes retType -> do
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
  
  (pos, Rec t param bindings body) -> do
    -- Check for duplicates
    checkDuplicates pos bindings
    
    -- Check that the type doesn't contain functions
    when (typeContainsAbs t) $
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
    
    pure $ Ann ((pos, t), Rec t param bindings' body')
