module OSC.Transforms.Optimize where

{-
-- NOTE: if bindings between two SAbs float collapse them into one
floatExpressions :: Map FuncRef Func -> Map FuncRef Func
floatExpressions = fmap go
  where
    go :: Func -> Func
    go (Func t params bindings body) = undefined

    isPure :: CExpr abs -> CExpr abs
    isPure = undefined

markPureExpressions :: Map FuncRef Func -> Map FuncRef Func
markPureExpressions = fmap go
  where
    go :: Func -> Func
    go (Func t params bindings body) = undefined

    isPure :: CExpr abs -> CExpr abs
    isPure = undefined
-}