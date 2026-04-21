{-# LANGUAGE KindSignatures #-}

module OSC.Transforms.AnnBind where

import Control.Monad.Trans.Class (lift)
import qualified Control.Monad.Reader as R
import qualified Control.Monad.Writer as W
import qualified Control.Monad.State as ST

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import OSC.Expr.Bitraversable
import OSC.Expr.Functors
import OSC.Expr.Comp (Ident (..), Type, paramTypes)
import qualified OSC.Expr.FoldSel as SRC
import qualified OSC.Expr.Comp as C
import OSC.Expr.AnnBind

--------------------------------------------------------------------------------

type CaptureM = R.ReaderT (Map Ident Ident, Map Ident Ident) (W.WriterT (Set Ident) (ST.State Int))

annCapturedBindings_ :: Ann Type SRC.Expr -> CaptureM (Ann Type Expr)
annCapturedBindings_ = bitraverse (rtraverse . trav) diff
  where
    nextName = do
      n <- ST.state $ \n -> (n, n + 1)
      pure $ Captured n
    
    trav _ (SRC.PVar n) = do
      (_, env) <- R.ask
    
      case M.lookup n env of
        Just subst -> do
          W.tell (S.singleton n)
          pure $ PVar subst
        Nothing -> pure $ PVar n
    trav rmap e = rmap e

    diff :: Diff (Ann Type SRC.Expr) -> CaptureM (Expr (Ann Type Expr))
    diff (PLam typ params bindings body) = do
      (prev, env) <- R.ask
   
      paramSubsts <- fmap M.fromList $ sequence [ (p,) <$> nextName | p <- params ]
      bindingsSubsts <- fmap M.fromList $ sequence [ (n,) <$> nextName | (n, _) <- bindings ]
   
      -- Process bindings recursively
      (bindings', capturedByBindings) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (paramSubsts <> bindingsSubsts, prev <> env) $ sequence
        [ (n,) <$> annCapturedBindings_ e
        | (n, e) <- bindings
        ]
   
      -- Process body recursively and capture free vars
      (body', capturedByBody) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (paramSubsts <> bindingsSubsts, prev <> env) (annCapturedBindings_ body)
   
      -- Propagate captures excluding params and bindings
      W.tell ((capturedByBindings <> capturedByBody) S.\\ (S.fromList $ M.keys (paramSubsts <> bindingsSubsts)))
   
      let allCaptured = capturedByBindings <> capturedByBody
   
      let bindings'' = mconcat
            [ [ if S.member n allCaptured
                  then (bindingsSubsts M.! n, C.AllocGlobal, Ann (t, e))
                  else (n, C.AllocLocal, Ann (t, e))
              | (n, Ann (t, e)) <- bindings'
              ]
            , [ (paramSubst, C.AllocGlobal, Ann (t, Expr $ C.Var p))
              | (p, t) <- zip params (paramTypes ("markCapturedBindings: " <> show typ) typ)
              , S.member p allCaptured
              , Just paramSubst <- [ M.lookup p paramSubsts ]
              ]
            ]
   
      -- Accumulate captured bindings
      pure $ PLamAnn typ params bindings'' body'
   
    diff (PRec typ delay param bindings body) = do
      (prev, env) <- R.ask
   
      paramSubstName <- nextName
      let paramSubst = M.singleton param paramSubstName

      bindingsSubsts <- fmap M.fromList $ sequence [ (n,) <$> nextName | (n, _) <- bindings ]
   
      -- Process bindings recursively
      (bindings', capturedByBindings) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (paramSubst <> bindingsSubsts, prev <> env) $ sequence
        [ (n,) <$> annCapturedBindings_ e
        | (n, e) <- bindings
        ]
   
      -- Process body recursively and capture free vars
      (body', capturedByBody) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (paramSubst <> bindingsSubsts, prev <> env) (annCapturedBindings_ body)
   
      -- Propagate captures excluding params and bindings
      W.tell ((capturedByBindings <> capturedByBody) S.\\ (S.fromList $ M.keys (paramSubst <> bindingsSubsts)))
      
      let allCaptured = capturedByBindings <> capturedByBody

      let bindings'' =
            [ if S.member n allCaptured
                then (bindingsSubsts M.! n, C.AllocGlobal, Ann (t, e))
                else (n, C.AllocLocal, Ann (t, e))
            | (n, Ann (t, e)) <- bindings'
            ]
   
      pure $ PRecAnn typ delay paramSubstName bindings'' body'

annCapturedBindings :: Ann Type SRC.Expr -> Ann Type Expr
annCapturedBindings = fst . flip ST.evalState 0 . W.runWriterT . flip R.runReaderT mempty . annCapturedBindings_

--------------------------------------------------------------------------------

data Pure = Pure | Impure
  deriving Eq

instance Monoid Pure where
  mempty = Pure

instance Semigroup Pure where
  Pure <> Pure = Pure
  _ <> _ = Impure

annPure :: Ann a Expr -> Ann (a, Pure) Expr
annPure (Ann (a, PConst n)) = Ann ((a, Pure), PConst n)
annPure (Ann (a, PArr elems)) = Ann ((a, mconcat [ p | Ann ((_, p), _) <- elems' ]), PArr elems')
  where
    elems' = fmap annPure elems
annPure (Ann (a, PFoldedSelectL elems idx)) = Ann ((a, purity), PFoldedSelectL elems' idx')
  where
    elems' = fmap annPure elems
    idx' = annPure idx
    purity = mconcat ([ p | Ann ((_, p), _) <- elems' ] ++ [p' | Ann ((_, p'), _) <- [idx']])
annPure (Ann (a, PFoldedSelectR expr elems)) = Ann ((a, purity), PFoldedSelectR expr' elems')
  where
    expr' = annPure expr
    elems' = fmap annPure elems
    purity = mconcat ([ p | Ann ((_, p), _) <- expr' : elems' ])
annPure (Ann (a, PLamAnn typ params bindings body)) = Ann ((a, purity), PLamAnn typ params bindings' body')
  where
    bindings' = [ (n, region, annPure e) | (n, region, e) <- bindings ]
    body' = annPure body
    purity = mconcat ([ p | (_, _, Ann ((_, p), _)) <- bindings' ] ++ [p' | Ann ((_, p'), _) <- [body']])
annPure (Ann (a, PRecAnn typ delay param bindings body)) = Ann ((a, Impure), PRecAnn typ delay param bindings' body')
  where
    bindings' = [ (n, region, annPure e) | (n, region, e) <- bindings ]
    body' = annPure body
annPure (Ann (a, POp op lhs rhs)) = Ann ((a, purity), POp op lhs' rhs')
  where
    lhs' = annPure lhs
    rhs' = annPure rhs
    purity = mconcat [ p | Ann ((_, p), _) <- [lhs', rhs'] ]
annPure (Ann (a, PVar ident)) = Ann ((a, Pure), PVar ident)
annPure (Ann (a, PApp func args)) = Ann ((a, purity), PApp func' args')
  where
    func' = annPure func
    args' = fmap annPure args
    purity = mconcat ([ p | Ann ((_, p), _) <- func' : args' ])
