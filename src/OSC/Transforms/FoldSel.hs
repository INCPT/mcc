module OSC.Transforms.FoldSel where

import qualified Control.Monad.State as ST

import OSC.Expr.Functors
import OSC.Expr.Bitraversable
import OSC.Expr.Comp (Type)
import OSC.Expr.FoldSel
import qualified OSC.Expr.AnnBind as SRC

--------------------------------------------------------------------------------

type FoldSelM = ST.State [Ann Type SRC.Expr]

push :: Ann Type SRC.Expr -> FoldSelM ()
push s = ST.modify (s:)

pop :: FoldSelM (Maybe (Ann Type SRC.Expr))
pop = do
  as <- ST.get
  case as of
    (a:as) -> do
      ST.put as
      pure (Just a)
    _ -> pure Nothing

foldSelections :: Ann Type SRC.Expr -> FoldSelM (Ann Type Expr)
foldSelections = bitraverse (\rmap expr@(Ann (exprt, _)) -> rtraverse (trav rmap exprt) expr) diff
  where
    trav _ _ (SRC.PArr elems) = do
     s <- pop
     case s of
       Just idx -> do
         elems' <- traverse foldSelections elems
         push idx
         PFoldedSelectL elems' <$> foldSelections idx
       Nothing -> PArr <$> traverse foldSelections elems

    trav rmap exprt expr = do
      idxs <- ST.get
      case idxs of
        [] -> rmap expr
        _ -> PFoldedSelectR <$> foldSelections (Ann (exprt, expr)) <*> traverse foldSelections idxs

    diff :: Diff (Ann Type SRC.Expr) -> FoldSelM (Expr (Ann Type Expr))
    diff (DSelect sel idx) = do
      push idx
      sel' <- foldSelections sel
      _ <- pop
      pure $ project sel'
