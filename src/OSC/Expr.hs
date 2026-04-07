{-# LANGUAGE LambdaCase #-}

module OSC.Expr where

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

typecheck :: Expr () -> GenM (Expr Type)
typecheck (EConst n) = pure $ EConst n

typecheck (EOp () op a b) = do
  a' <- typecheck a
  b' <- typecheck b
  case (op, exprType a', exprType b') of
    (Add, TNumber t, TNumber u)
      | t /= u -> E.throwError $ TypeError $ "typecheck: +: mismatched types: " <> show t <> ", " <> show u
      | otherwise -> pure $ EOp (TNumber t) o a' b'

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

typecheck _ = undefined

bindings :: Map Ident (Expr ()) -> GenM (Map Ident (Expr Type))
bindings m
  | Just e <- reccheck m = E.throwError e
  | otherwise = do
      undefined

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
