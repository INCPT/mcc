module OSC.Transforms.FoldSel where

import qualified Control.Monad.State as ST

import OSC.Expr.Functors
import OSC.Expr.Bitraversable
import OSC.Expr.Comp (Type(..))
import OSC.Expr.FoldSel
import qualified OSC.Expr.Base as SRC

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

foldSelections :: Ann Type SRC.Expr -> Ann Type Expr
foldSelections = flip ST.evalState [] . foldSelections_

foldSelections_ :: Ann Type SRC.Expr -> FoldSelM (Ann Type Expr)
foldSelections_ = bitraverse trav diff
  where
    peelOffIndices :: Int -> Type -> Type
    peelOffIndices 0 t = t
    peelOffIndices n (TArr t _) = peelOffIndices (n - 1) t
    peelOffIndices n t = error $ "cexprType: cannot peel " <> show n <> " indices from type " <> show t <> " (this is a bug)"

    trav _ (Ann (t, SRC.PArr elems)) = do
     s <- pop
     case s of
       Just idx -> do
         elems' <- traverse foldSelections_ elems
         push idx
         pure $ Ann (t, PFoldedSelectL elems' (foldSelections idx))
       Nothing -> pure $ Ann (t, PArr $ fmap foldSelections elems)

    trav rmap expr@(Ann (t, _)) = do
      idxs <- ST.get
      case idxs of
        [] -> rtraverse rmap expr
        _ -> pure $ Ann (peelOffIndices (length idxs) t, PFoldedSelectR (foldSelections expr) (fmap foldSelections idxs))

    diff :: Diff (Ann Type SRC.Expr) -> FoldSelM (Expr (Ann Type Expr))
    diff (DSelect sel idx) = do
      push idx
      sel' <- foldSelections_ sel
      _ <- pop
      pure $ project sel'
