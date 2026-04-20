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

type CaptureM = R.ReaderT (Map Ident (Maybe Ident), Map Ident (Maybe Ident)) (W.WriterT (Set Ident) (ST.State Int))

annCapturedBindings_ :: Ann Type SRC.Expr -> CaptureM (Ann Type Expr)
annCapturedBindings_ = bitraverse (rtraverse . trav) diff
  where
    nextName = do
      n <- ST.state $ \n -> (n, n + 1)
      pure $ Ident $ "_captured_" <> show n
    
    trav _ (SRC.PVar n) = do
      (_, env) <- R.ask
    
      case M.lookup n env of
        Just (Just subst) -> do
          W.tell (S.singleton n)
          pure $ PVar subst
        Just Nothing -> do
          W.tell (S.singleton n)
          pure $ PVar n
        Nothing -> pure $ PVar n
    trav rmap e = rmap e

    diff :: Diff (Ann Type SRC.Expr) -> CaptureM (Expr (Ann Type Expr))
    diff (PLam t params bindings body) = do
      (prev, env) <- R.ask
   
      let bindingNames = M.fromList (fmap ((,Nothing) . fst) bindings)
      
      paramSubsts <- fmap M.fromList $ sequence [ (p,) <$> Just <$> nextName | p <- params ]
   
      -- Process bindings recursively
      (bindings', capturedByBindings) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (paramSubsts <> bindingNames, prev <> env) $ sequence
        [ (n,) <$> annCapturedBindings_ e
        | (n, e) <- bindings
        ]
   
      -- Process body recursively and capture free vars
      (body', capturedByBody) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (paramSubsts <> bindingNames, prev <> env) (annCapturedBindings_ body)
   
      -- Propagate captures excluding params and bindings
      W.tell ((capturedByBindings <> capturedByBody) S.\\ (S.fromList $ M.keys (paramSubsts <> bindingNames)))
   
      let allCaptured = capturedByBindings <> capturedByBody
   
      let bindings'' = mconcat
            [ [ (n, if S.member n allCaptured then C.Global else C.Local, Ann (t, e))
              | (n, Ann (t, e)) <- bindings'
              ]
            , [ (paramSubst, C.Global, Ann (t, Expr $ C.Var p))
              | (p, t) <- zip params (paramTypes ("markCapturedBindings: " <> show t) t)
              , S.member p allCaptured
              , Just (Just paramSubst) <- [ M.lookup p paramSubsts ]
              ]
            ]
   
      -- Accumulate captured bindings
      pure $ PLamAnn t params bindings'' body'
   
    diff (PRec t delay param bindings body) = do
      (prev, env) <- R.ask
   
      paramSubstName <- nextName
      let paramSubst = M.singleton param (Just paramSubstName)
      let bindingNames = M.fromList (fmap ((, Nothing) . fst) bindings)
   
      -- Process bindings recursively
      (bindings', capturedByBindings) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (paramSubst <> bindingNames, prev <> env) $ sequence
        [ (n,) <$> annCapturedBindings_ e
        | (n, e) <- bindings
        ]
   
      -- Process body recursively and capture free vars
      (body', capturedByBody) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (paramSubst <> bindingNames, prev <> env) (annCapturedBindings_ body)
   
      -- Propagate captures excluding params and bindings
      W.tell ((capturedByBindings <> capturedByBody) S.\\ (S.fromList $ M.keys (paramSubst <> bindingNames)))
      
      let allCaptured = capturedByBindings <> capturedByBody

      let bindings'' =
            [ (n, if S.member n allCaptured then C.Global else C.Local, Ann (t, e))
            | (n, Ann (t, e)) <- bindings'
            ]
   
      pure $ PRecAnn t delay paramSubstName bindings'' body'

annCapturedBindings :: Ann Type SRC.Expr -> Ann Type Expr
annCapturedBindings = fst . flip ST.evalState 0 . W.runWriterT . flip R.runReaderT mempty . annCapturedBindings_
