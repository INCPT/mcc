module OSC.Expr where

import qualified Control.Monad.Except as E
import qualified Control.Monad.Reader as R

import Data.Generics.Uniplate.Data
import Data.Generics.Str

import Data.Map (Map)
import qualified Data.Map as M

import OSC.Ctx

data TypeError = TypeError String

type GenM = E.ExceptT TypeError (R.Reader (Map Ident Type))

holes :: [a] -> (a, [a])
holes = undefined

reccheck :: Map Ident (Expr ()) -> GenM ()
reccheck = undefined

typecheck :: Map Ident (Expr ()) -> GenM (Map Ident (Expr Type))
typecheck = undefined

-- i32 :: Int -> GenM (Expr t)
-- i32 = pure . EConst . I32
-- 
-- f32 :: Float -> GenM (Expr t)
-- f32 = pure . EConst . F32
-- 
-- i64 :: Int -> GenM (Expr t)
-- i64 = pure . EConst . I64
-- 
-- f64 :: Double -> GenM (Expr t)
-- f64 = pure . EConst . F64
-- 
-- op :: Op -> GenM (Expr t) -> GenM (Expr t) -> GenM (Expr t)
-- op o a b = do
--   a' <- a
--   b' <- b
--   case (o, exprType a', exprType b') of
--     (Add, TNumber t, TNumber u)
--       | t /= u -> E.throwError $ TypeError $ "+: mismatched types: " <> show t <> ", " <> show u
--       | otherwise -> pure $ EOp (TNumber t) o a' b'
-- 
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