{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecursiveDo #-}

module OSC.Expr where

import Control.Monad (when)
import qualified Control.Monad.Except as E
import qualified Control.Monad.Reader as R
import qualified Control.Monad.State as S

import Data.Generics.Uniplate.Data
import Data.Generics.Str

import Data.Foldable (msum)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import OSC.Ctx

newtype TypeError = TypeError String
  deriving Show

type GenM = E.ExceptT TypeError (R.Reader (Map Ident Type))

reccheck :: Map Ident (Expr ()) -> Maybe TypeError
reccheck m = msum [ visit n ns | (n, ns) <- M.toList vars ]
  where
    vars = fmap (\expr -> S.fromList [ n | EVar _ n <- universe expr ]) m

    visit :: Ident -> Set Ident -> Maybe TypeError
    visit n ns
      | S.member n ns = Just $ TypeError $ "reccheck: recursive bindings: " <> show n <> ", " <> show ns
      | otherwise = msum [ visit ref ns' | ref <- S.toList (M.findWithDefault mempty n vars) ]
          where
            ns' = S.insert n ns

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

{-
data Op = Add | Sub | Mul | Div | Mod | And | Or | Xor | Shl | Shr | Rotl | Rotr 
        | Eq | Ne | Gt | Lt | GEt | LEt 
        | Min | Max | CopySign | Rem
-}

  case (op, exprType a', exprType b') of
    (Add, TNumber t, TNumber u)
      | t /= u -> E.throwError $ TypeError $ "typecheck: +: mismatched types: " <> show t <> ", " <> show u
      | otherwise -> pure $ EOp (TNumber t) op a' b'

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

  bindings' <- R.local (\env -> paramsEnv <> env) $ typecheckBindings (M.fromList bindings)
  body' <- R.local (\env -> fmap exprType bindings' <> paramsEnv <> env) $ typecheck body
  pure $ EAbs t params (M.toList bindings') body'

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
  bindings' <- R.local (\env -> paramsEnv <> env) $ typecheckBindings (M.fromList bindings)
  body' <- R.local (\env -> fmap exprType bindings' <> paramsEnv <> env) $ typecheck body

  let paramsEnv = M.singleton param (exprType body')

  pure $ ERec (exprType body') delay param (M.toList bindings') body'

typecheckBindings :: Map Ident (Expr ()) -> GenM (Map Ident (Expr Type))
typecheckBindings bindings
  | Just e <- reccheck bindings = E.throwError e
  | otherwise = mdo
      bindings' <- R.local (\env -> bindingsEnv <> env) $ traverse typecheck bindings
      let bindingsEnv = fmap exprType bindings'

      pure bindings'

--------------------------------------------------------------------------------

i32 :: Int -> Expr ()
i32 = EConst . I32

f32 :: Float -> Expr ()
f32 = EConst . F32

i64 :: Int -> Expr ()
i64 = EConst . I64

f64 :: Double -> Expr ()
f64 = EConst . F64

-- arr :: [GenM (Expr t)] -> GenM (Expr t)
-- arr [] = E.throwError $ TypeError "empty array"
-- arr (a:as) = do
--   a' <- a
--   as' <- sequence as
--   let at = exprType a'
--   if all ((== at) . exprType) as'
--     then pure $ EArr (TArr at (length as + 1)) (a':as')
--     else E.throwError $ TypeError $ "arr: mismatched types: " <> show (at:fmap exprType as')
-- 
-- var :: Ident -> GenM (Expr t)
-- var = undefined
-- 
-- bindings :: [(Ident, GenM (Expr t))] -> GenM [(Ident, (Expr t))]
-- bindings = undefined
