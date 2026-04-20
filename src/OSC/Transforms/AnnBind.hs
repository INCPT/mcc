{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

module OSC.Transforms.AnnBind where

import Control.Monad (when)
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
import qualified OSC.Expr.Base as B
import qualified OSC.Expr.Comp as C
import OSC.Expr.AnnBind

--------------------------------------------------------------------------------

type CaptureM = R.ReaderT (Map Ident (Maybe Ident), Map Ident (Maybe Ident)) (W.WriterT (Set Ident) (ST.StateT Int (ST.State (Map Ident Type))))

runCapture :: CaptureM a -> ((a, Set Ident), Map Ident Type)
runCapture = flip ST.runState mempty . flip ST.evalStateT 0 . W.runWriterT . flip R.runReaderT mempty

markCapturedBindings :: Ann Type B.Expr -> CaptureM (Ann Type Expr)
markCapturedBindings e@(Ann (t, _)) = bitraverse (rtraverse . trav) diff e
  where
    nextName = do
      n <- ST.state $ \n -> (n, n + 1)
      pure $ Ident $ "_captured_" <> show n
    
    trav _ (B.PVar n) = do
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

    diff :: Diff (Ann Type B.Expr) -> CaptureM (Expr (Ann Type Expr))
    diff (PLam t params bindings body) = do
      (prev, env) <- R.ask
   
      let bindingNames = M.fromList (fmap ((,Nothing) . fst) bindings)
      
      paramSubsts <- fmap M.fromList $ sequence [ (p,) <$> Just <$> nextName | p <- params ]
   
      -- Process bindings recursively
      (bindings', capturedByBindings) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (paramSubsts <> bindingNames, prev <> env) $ sequence
        [ (n,) <$> markCapturedBindings e
        | (n, e) <- bindings
        ]
   
      -- Process body recursively and capture free vars
      (body', capturedByBody) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (paramSubsts <> bindingNames, prev <> env) (markCapturedBindings body)
   
      -- Propagate captures excluding params and bindings
      W.tell ((capturedByBindings <> capturedByBody) S.\\ (S.fromList $ M.keys (paramSubsts <> bindingNames)))
   
      let allCaptured = capturedByBindings <> capturedByBody
   
      bindings'' <- sequence $ mconcat
        [ [ do
              when (S.member n allCaptured) $ lift $ lift $ lift $ ST.modify (M.insert n t)
              pure (n, if S.member n allCaptured then C.Global else C.Local, Ann (t, e))
          | (n, Ann (t, e)) <- bindings'
          ]
        , [ do
              lift $ lift $ lift $ ST.modify (M.insert paramSubst t)
              pure (paramSubst, C.Global, Ann (t, Expr $ C.Var p))
          | (p, t) <- zip params (paramTypes ("markCapturedBindings: " <> show t) t)
          , S.member p allCaptured
          , Just (Just paramSubst) <- [ M.lookup p paramSubsts ]
          ]
        ]
   
      -- Accumulate captured bindings
      pure $ PLamAnn t params bindings'' body'
   
    diff (PRec t delay param bindings body) = do
      (prev, env) <- R.ask
   
      paramSubst <- M.singleton <$> pure param <*> Just <$> nextName
      let bindingNames = M.fromList (fmap ((, Nothing) . fst) bindings)
   
      -- Process bindings recursively
      (bindings', capturedByBindings) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (paramSubst <> bindingNames, prev <> env) $ sequence
        [ (n,) <$> markCapturedBindings e
        | (n, e) <- bindings
        ]
   
      -- Process body recursively and capture free vars
      (body', capturedByBody) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (paramSubst <> bindingNames, prev <> env) (markCapturedBindings body)
   
      -- Propagate captures excluding params and bindings
      W.tell ((capturedByBindings <> capturedByBody) S.\\ (S.fromList $ M.keys (paramSubst <> bindingNames)))
      
      let allCaptured = capturedByBindings <> capturedByBody
   
      bindings'' <- sequence $ mconcat
        [ [ do
              when (S.member n allCaptured) $ lift $ lift $ lift $ ST.modify (M.insert n t)
              pure (n, if S.member n allCaptured then C.Global else C.Local, Ann (t, e))
          | (n, Ann (t, e)) <- bindings'
          ]
        , [ do
              lift $ lift $ lift $ ST.modify (M.insert paramSubst t)
              pure (paramSubst, C.Global, Ann (t, Expr $ C.Var p))
          | (p, t) <- zip [param] [t]
          , S.member p allCaptured
          , Just (Just paramSubst) <- [ M.lookup p paramSubst ]
          ]
        ]
   
      pure $ PRecAnn t delay param bindings'' body'