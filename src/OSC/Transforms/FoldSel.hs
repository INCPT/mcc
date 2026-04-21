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

-- | Pair each index with the appropriate array, so an an expression like
-- `[[0, 1], [2, 3]][1][0]` turns into `[[0, 1][0], [2, 3][0]][1]`.
-- This allows for easy constant index elimination and the generation of more
-- efficient code.
foldSelections :: Ann Type SRC.Expr -> Ann Type Expr
foldSelections = flip ST.evalState [] . foldSelections_

foldSelections_ :: Ann Type SRC.Expr -> FoldSelM (Ann Type Expr)
foldSelections_ = bitraverse trav diff
  where
    peelOffIndices :: Int -> Type -> Type
    peelOffIndices 0 t = t
    peelOffIndices n (TArr t _) = peelOffIndices (n - 1) t
    peelOffIndices n t = error $ "cexprType: cannot peel " <> show n <> " indices from type " <> show t <> " (this is a bug)"

    trav _ (Ann (typ, SRC.PArr elems)) = do
     s <- pop
     case s of
       Just idx -> do
         elems' <- traverse foldSelections_ elems
         push idx
         pure $ Ann (typ, PFoldedSelectL elems' (foldSelections idx))
       Nothing -> pure $ Ann (typ, PArr $ fmap foldSelections elems)

    trav rmap expr@(Ann (typ, _)) = do
      idxs <- ST.get
      case idxs of
        [] -> rtraverse rmap expr
        _ -> pure $ Ann (peelOffIndices (length idxs) typ, PFoldedSelectR (foldSelections expr) (fmap foldSelections idxs))

    diff :: Diff (Ann Type SRC.Expr) -> FoldSelM (Expr (Ann Type Expr))
    diff (DSelect sel idx) = do
      push idx
      sel' <- foldSelections_ sel
      _ <- pop
      pure $ project sel'

{-
-- TODO: this must happen after inlining / CSE (otherwise things like let a = [1, 2, 3] in a[0] won't be optimized)
elimConstIndices :: CExpr Abs -> CExpr Abs
elimConstIndices = transformCExpr (\_ -> id) id go
  where
    go :: CExpr Abs -> CExpr Abs

    -- Eliminate constant index selections by directly selecting the choice
    -- It's ok to prune impure expressions here (since the index is constant those expressions will never be accessible)
    go (CSel _ chs (CConst (I32 idx))) = chs !! idx
    go (CSel _ chs (CConst (I64 idx))) = chs !! idx

    -- Keep everything else as-is
    go ch = ch
-}