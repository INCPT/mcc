{-# LANGUAGE OverloadedRecordDot #-}

module OSC.Transforms.Defunc where

import qualified Control.Monad.State as ST
import qualified Data.Map as M

import OSC.Expr.Bitraversable
import qualified OSC.Expr.Comp as C
import OSC.Expr.Functors
import qualified OSC.Expr.AnnBind as SRC
import OSC.Expr.Defunc

data DefuncMap f = DefuncMap
  { funcMap :: M.Map FuncRef (C.LamAnn (f Expr))
  , recs :: [C.RecAnn (f Expr)]
  }

type DefuncM f = ST.State (Int, DefuncMap f)

defunc_ :: RFunctor f => f SRC.Expr -> DefuncM f (f Expr)
defunc_ = bitraverse rtraverse diff
  where
    diff (LamAnn lam) = do
      lam' <- traverse defunc_ lam
      fr <- ST.state $ \(fr, dfm) -> (FuncRef (fr + 1), (fr + 1, dfm { funcMap = M.insert (FuncRef fr) lam' dfm.funcMap }))
      pure $ Func fr
    diff (RecAnn rec_@(C.RecAnn _ _ param _ _)) = do
      rec_' <- traverse defunc_ rec_
      ST.modify $ \(fr, dfm) -> (fr, dfm { recs = rec_':dfm.recs })
      pure $ Rec param

defunc :: RFunctor f => f SRC.Expr -> (f Expr, DefuncMap f)
defunc = fmap snd . flip ST.runState (0, DefuncMap mempty mempty) . defunc_