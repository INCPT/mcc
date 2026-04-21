{-# LANGUAGE OverloadedRecordDot #-}

module OSC.Transforms.Defunc where

import qualified Control.Monad.State as ST
import qualified Data.Map as M

import OSC.Expr.Bitraversable
import qualified OSC.Expr.Comp as C
import OSC.Expr.Functors
import qualified OSC.Expr.AnnBind as SRC
import OSC.Expr.Defunc

type DefuncM f = ST.State (Int, DefuncMap f)

propagate :: (M.Map k b -> a -> b) -> M.Map k a -> M.Map k b
propagate f m = let m' = fmap (f m') m in m'

defunc_ :: RFunctor f => f SRC.Expr -> DefuncM f (f Expr)
defunc_ = bitraverse rtraverse diff
  where
    diff (LamAnn lam) = do
      fr <- ST.state $ \(fr, dfm) -> (FuncRef fr, (fr + 1, dfm))
      lam' <- traverse defunc_ lam
      ST.modify $ \(fr, dfm) -> (fr, dfm { funcMap = M.insert (FuncRef fr) lam' dfm.funcMap })
      pure $ Func fr
    diff (RecAnn rec_@(C.RecAnn _ _ param _ _)) = do
      rec_' <- traverse defunc_ rec_
      ST.modify $ \(fr, dfm) -> (fr, dfm { recs = rec_':dfm.recs })
      pure $ Rec param

defunc :: RFunctor f => f SRC.Expr -> (f Expr, DefuncMap f)
defunc = fmap snd . flip ST.runState (0, DefuncMap mempty mempty) . defunc_