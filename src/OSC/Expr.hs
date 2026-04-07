module OSC.Expr where

import qualified Control.Monad.Except as E

import OSC.Ctx

data TypeError = TypeError String

type GenM = E.Except TypeError

i32 :: Int -> GenM Expr
i32 = pure . EConst . I32

f32 :: Float -> GenM Expr
f32 = pure . EConst . F32

i64 :: Int -> GenM Expr
i64 = pure . EConst . I64

f64 :: Double -> GenM Expr
f64 = pure . EConst . F64

op :: Op -> GenM Expr -> GenM Expr -> GenM Expr
op o a b = do
  a' <- a
  b' <- b
  case (o, exprType a', exprType b') of
    (Add, TNumber t, TNumber u)
      | t /= u -> E.throwError $ TypeError $ "+: mismatched types: " <> show t <> ", " <> show u
      | otherwise -> pure $ EOp (TNumber t) o a' b'

arr :: [GenM Expr] -> GenM Expr
arr [] = E.throwError $ TypeError "empty array"
arr (a:as) = do
  a' <- a
  as' <- sequence as
  let at = exprType a'
  if all ((== at) . exprType) as'
    then pure $ EArr (TArr at (length as + 1)) (a':as')
    else E.throwError $ TypeError $ "arr: mismatched types: " <> show (at:fmap exprType as')