module OSC.Transforms.FoldSel where

import qualified Control.Monad.State as ST

import OSC.Expr.Functors
import OSC.Expr.Bitraversable
import OSC.Expr.Comp (Type)
import OSC.Expr.FoldSel
import qualified OSC.Expr.AnnBind as SRC

--------------------------------------------------------------------------------

{-
type FoldSelectionsM = Stack (Type, Term Sig0) (Term Sig1)

foldSelections :: Term Sig0 -> Term Sig1
foldSelections = runStack . expr
  where
    rhs :: Term Sig1 -> FoldSelectionsM
    rhs expr = do
      idxs <- ST.get
      case idxs of
        [] -> pure expr
        _ -> pure $ inject $ FoldedSelectR expr (fmap (foldSelections . snd) idxs)

    expr :: Term Sig0 -> FoldSelectionsM
    expr term = case project term of
      -- Handle Value constructors
      Just (Const n) -> rhs $ inject (Const n)
      Just (Arr es) -> do
        s <- pop
        case s of
          Just (t, idx) -> do
            es' <- traverse expr es
            push (t, idx)
            pure $ inject $ FoldedSelectL es' (foldSelections idx)
          Nothing -> pure $ inject $ Arr (fmap foldSelections es)
      
      -- Handle Exp constructors
      Nothing -> case project term of
        Just (Op a b) -> rhs $ inject $ Op (foldSelections a) (foldSelections b)
        Just (Var n) -> rhs $ inject $ Var n
        Just (App f args) -> rhs $ inject $ App (foldSelections f) (fmap foldSelections args)
        
        -- Handle Lam constructor
        Nothing -> case project term of
          Just (Lam params locals body) -> 
            rhs $ inject $ Lam params (fmap (fmap foldSelections) locals) (foldSelections body)
          
          -- Handle Select constructor
          Nothing -> case project term of
            Just (Select sel idx) -> do
              push (exprType term, idx)
              sel' <- expr sel
              _ <- pop
              pure sel'
            Nothing -> error "foldSelections: unknown constructor"

    exprType :: Term Sig0 -> Type
    exprType term = case project term of
      Just (Const _) -> TNumber TI32  -- Assuming constants are I32
      Just (Arr es) -> case es of
        [] -> error "exprType: empty array"
        (e:_) -> TArr (exprType e) (length es)
      Nothing -> case project term of
        Just (Op _ _) -> TNumber TI32  -- Assuming ops return I32
        Just (Var _) -> error "exprType: cannot determine type of variable"
        Just (App _ _) -> error "exprType: cannot determine type of application"
        Nothing -> case project term of
          Just (Lam _ _ _) -> error "exprType: cannot determine type of lambda"
          Nothing -> case project term of
            Just (Select e _) -> peelType (exprType e)
            Nothing -> error "exprType: unknown constructor"
    
    peelType :: Type -> Type
    peelType (TArr t _) = t
    peelType t = error $ "peelType: cannot peel type " ++ show t
-}

type FoldSelM = ST.State [(Type, Ann Type SRC.Expr)]

foldSelections :: Ann Type SRC.Expr -> FoldSelM (Ann Type Expr)
foldSelections = bitraverse rtraverse diff
  where
    diff :: Diff (Ann Type SRC.Expr) -> FoldSelM (Expr (Ann Type Expr))
    diff = undefined