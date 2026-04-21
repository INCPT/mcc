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
annPure expr = pile expr purity
  where
    extract = snd . fst . unAnn . annPure

    purity :: Expr (Ann a Expr) -> Pure
    purity (PConst _) = Pure
    purity (PArr elems) = mconcat [ extract e | e <- elems ]
    purity (PFoldedSelectL elems idx) = mconcat $ [ extract e | e <- elems ] <> [ extract idx ]
    purity (PFoldedSelectR expr elems) = mconcat [ extract e | e <- expr:elems ]
    purity (PLamAnn _ _ bindings body) = mconcat $ [ extract e | (_, _, e) <- bindings ] <> [ extract body ]
    purity (PRecAnn _ _ _ _ _) = Impure
    purity (POp _ lhs rhs) = mconcat [ extract e | e <- [lhs, rhs] ]
    purity (PVar _) = Pure
    purity (PApp func args) = mconcat [ extract e | e <- func:args ]
