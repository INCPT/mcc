module OSC.Transforms.Defunc where

import qualified Control.Monad.State as ST
import qualified Data.Map as M

import OSC.Expr.Bitraversable
import qualified OSC.Expr.Comp as C
import OSC.Expr.Comp (FuncRef)
import OSC.Expr.Functors
import qualified OSC.Expr.AnnBind as SRC
import OSC.Expr.Defunc

type DefuncM f = ST.State (Int, M.Map FuncRef (C.LamAnn (f (Expr))))

defunc_ :: RFunctor f => f SRC.Expr -> DefuncM f (f Expr)
defunc_ = bitraverse rtraverse diff
  where
    diff (LamAnn lam) = do
      lam' <- traverse defunc_ lam
      fr <- ST.state $ \(fr, m) -> (C.FuncRef (fr + 1), (fr + 1, M.insert (C.FuncRef fr) lam' m))
      pure $ FuncRef fr

defunc :: RFunctor f => f SRC.Expr -> (f Expr, M.Map FuncRef (C.LamAnn (f (Expr))))
defunc = fmap snd . flip ST.runState (0, mempty) . defunc_