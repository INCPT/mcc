module OSC.Transforms.FoldSel where

import qualified Control.Monad.State as ST

import OSC.Expr.Functors
import OSC.Expr.Bitraversable
import OSC.Expr.Comp (Type)
import OSC.Expr.FoldSel
import qualified OSC.Expr.AnnBind as SRC

type FoldSelM = ST.State [(Type, Ann Type SRC.Expr)]

foldSelections :: Ann Type SRC.Expr -> FoldSelM (Ann Type Expr)
foldSelections = bitraverse rtraverse diff
  where
    diff :: Diff (Ann Type SRC.Expr) -> FoldSelM (Expr (Ann Type Expr))
    diff = undefined