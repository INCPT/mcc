{-# LANGUAGE TupleSections #-}

module OSC.Transforms.AnnBind where

import Control.Monad (when, unless)
import Control.Monad.Identity (Identity(..), runIdentity)
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
import OSC.Expr.Comp (Ident, Type)
import qualified OSC.Expr.Base as B
import OSC.Expr.AnnBind

--------------------------------------------------------------------------------

type CaptureM = R.ReaderT (Set Ident) (W.WriterT (Set Ident) (ST.State (Map Ident Type)))

runCapture :: CaptureM a -> ((a, Set Ident), Map Ident Type)
runCapture = runIdentity . flip ST.runStateT mempty . W.runWriterT . flip R.runReaderT mempty

markCapturedBindings :: Type -> B.Expr (Ann Type B.Expr) -> CaptureM (Expr (Ann Type Expr))
markCapturedBindings _ (B.Var n) = do
  env <- R.ask

  -- Add to captured set if var doesn't reference the params or bindings of the current lambda/rec block
  unless (S.member n env) $ W.tell (S.singleton n)
  pure (Var n)

markCapturedBindings _ e = bitraverse (flow markCapturedBindings) go e
  where
    flow f (Ann (t, e)) = Ann <$> (t,) <$> f t e

    go :: Diff (Ann Type B.Expr) -> CaptureM (Expr (Ann Type Expr))
    go (DLam t params bindings body) = do
      let paramsEnv = S.fromList params
      let bindingNames = S.fromList (fmap fst bindings)

      -- Process bindings recursively
      (bindings', capturedByBindings) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (paramsEnv <> bindingNames) $ sequence
        [ (n,) <$> flow markCapturedBindings e
        | (n, e) <- bindings
        ]

      -- Process body recursively and capture free vars
      (body', capturedByBody) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (paramsEnv <> bindingNames) (flow markCapturedBindings body)

      -- Propagate captures excluding params and bindings
      W.tell ((capturedByBindings <> capturedByBody) S.\\ (paramsEnv <> bindingNames))

      let allCaptured = capturedByBindings <> capturedByBody

      bindings'' <- sequence
        [ do
            when (S.member n allCaptured) $ ST.modify (M.insert n t)
            pure (n, if S.member n allCaptured then Global else Local, Ann (t, e))
        | (n, Ann (t, e)) <- bindings'
        ]

      -- Accumulate captured bindings
      pure $ LamAnn t params bindings'' body'

    go (DRec t delay param bindings body) = do
      let paramEnv = S.singleton param
      let bindingNames = S.fromList (fmap fst bindings)

      -- Process bindings recursively
      (bindings', capturedByBindings) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (paramEnv <> bindingNames) $ sequence
        [ (n,) <$> flow markCapturedBindings e
        | (n, e) <- bindings
        ]

      -- Process body recursively and capture free vars
      (body', capturedByBody) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (paramEnv <> bindingNames) (flow markCapturedBindings body)

      -- Propagate captures excluding params and bindings
      W.tell ((capturedByBindings <> capturedByBody) S.\\ (paramEnv <> bindingNames))
      
      let allCaptured = capturedByBindings <> capturedByBody
      
      bindings'' <- sequence
        [ do
            when (S.member n allCaptured) $ ST.modify (M.insert n t)
            pure (n, if S.member n allCaptured then Global else Local, Ann (t, e))
        | (n, Ann (t, e)) <- bindings'
        ]

      pure $ RecAnn t delay param bindings'' body'
