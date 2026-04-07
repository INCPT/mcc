{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TupleSections #-}

module OSC.Expr where

import Control.Monad (when)
import qualified Control.Monad.Except as E
import qualified Control.Monad.Reader as R

import Data.Generics.Uniplate.Data (universe)

import Data.Foldable (msum)
import Data.Graph (Graph, Vertex, graphFromEdges, reachable, topSort)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import OSC.Ctx

newtype TypeError = TypeError String
  deriving Show

type GenM = E.ExceptT TypeError (R.Reader (Map Ident Type))

reccheck :: [(Ident, Expr ())] -> Either TypeError [(Ident, Expr ())]
reccheck bindings =
  case findCycle graph of
    Just ident -> Left $ TypeError $ "reccheck: cyclic dependency involving: " <> show ident
    Nothing -> Right [ (ident, bindingsMap M.! ident) | v <- reverse (topSort graph), let (_, ident, _) = nodeFromVertex v ]
  where
    bindingsMap = M.fromList bindings
    vars = fmap (\expr -> S.fromList [ n | EVar _ n <- universe expr ]) bindingsMap
    
    edges = [ (ident, ident, S.toList deps) | (ident, deps) <- M.toList vars ]
    (graph, nodeFromVertex, _) = graphFromEdges edges
    
    findCycle :: Graph -> Maybe Ident
    findCycle g = msum [ checkVertex v | v <- [0 .. length edges - 1] ]
      where
        checkVertex v =
          let (_, ident, _) = nodeFromVertex v
          in if v `elem` reachable g v
             then Just ident
             else Nothing

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

-- TODO: allow shadowing only if exprs of different type?
---- this means shadowcheck must happen after typechecking
---- and also in reccheck we can't indiscriminately collect EVars; nested bindings must reset the reccheck

shadowcheck :: Map Ident (Expr ()) -> Maybe TypeError
shadowcheck = undefined

--------------------------------------------------------------------------------

treturnType :: E.MonadError TypeError m => Type -> m Type
treturnType (TAbs _ t) = pure t
treturnType t = E.throwError $ TypeError $ "returnType: not an abstraction: " <> show t

tpeelType :: E.MonadError TypeError m => Type -> m Type
tpeelType (TArr t _) = pure t
tpeelType t = E.throwError $ TypeError $ "peelType: not an array: " <> show t

tparamTypes :: E.MonadError TypeError m => Type -> m [Type]
tparamTypes (TAbs params _) = pure params
tparamTypes t = E.throwError $ TypeError $ "paramTypes: not an abstraction" <> show t

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
  ptypes <- tparamTypes t
  let paramsEnv = M.fromList (zip params ptypes)

  bindings' <- R.local (\env -> paramsEnv <> env) $ typecheckBindings bindings
  body' <- R.local (\env -> M.fromList (fmap (fmap exprType) bindings') <> paramsEnv <> env) $ typecheck body
  pure $ EAbs t params bindings' body'

typecheck (EApp () f params) = do
  f' <- typecheck f
  params' <- traverse typecheck params

  ptypes <- tparamTypes (exprType f')
  rtype <- treturnType (exprType f')

  sequence_
    [ when (fpt /= pt) $ E.throwError $ TypeError $ "typecheck: type mismatch in function application: " <> show fpt <> " <=> " <> show pt
    | (fpt, pt) <- zip ptypes (fmap exprType params')
    ]

  case drop (length params) ptypes of
    [] -> pure $ EApp rtype f' params'
    remparams -> pure $ EApp (TAbs remparams rtype) f' params'

typecheck (ESelect () expr sel) = do
  expr' <- typecheck expr
  sel' <- typecheck sel

  t <- tpeelType (exprType expr')
  
  case exprType sel' of
    TNumber TI32 -> pure ()
    TNumber TI64 -> pure ()
    t -> E.throwError $ TypeError $ "typecheck: selection index not an integer: " <> show t
  
  pure $ ESelect t expr' sel'

typecheck (ERec () delay param bindings body) = mdo
  bindings' <- R.local (\env -> paramsEnv <> env) $ typecheckBindings bindings
  body' <- R.local (\env -> M.fromList (fmap (fmap exprType) bindings') <> paramsEnv <> env) $ typecheck body

  let t = exprType body'
  let paramsEnv = M.singleton param t
  
  when (typeContainsAbs t) $ E.throwError $ TypeError $ "typecheck: return type contains abstractions: " <> show t

  pure $ ERec t delay param bindings' body'
  where
    typeContainsAbs (TNumber _) = False
    typeContainsAbs (TArr t _) = typeContainsAbs t
    typeContainsAbs (TAbs _ _) = True

typecheckBindings :: [(Ident, Expr ())] -> GenM [(Ident, Expr Type)]
typecheckBindings bindings
  | Just e <- dupcheck bindings = E.throwError e
  | Left e <- reccheck bindings = E.throwError e
  | otherwise = mdo
      bindings' <- R.local (\env -> bindingsEnv <> env) $ sequenceA [ (n,) <$> typecheck expr | (n, expr) <- bindings ]
      let bindingsEnv = M.fromList $ fmap (fmap exprType) bindings'

      pure bindings'

infer :: [(Ident, Expr ())] -> Either TypeError [(Ident, Expr Type)]
infer = flip R.runReader mempty . E.runExceptT . typecheckBindings

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

select :: Expr () -> Expr () -> Expr ()
select = ESelect ()

rec_ :: Int -> Ident -> [(Ident, Expr ())] -> Expr () -> Expr ()
rec_ = ERec ()

--------------------------------------------------------------------------------

es :: [(Ident, Expr ())]
es = 
  [ ("x", i32 5)
  , ("y", var "x")
  ]

t1 = infer
  [ ("x", i32 5)
  , ("y", var "x")
  ]
