{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module OSC.Transforms.AnnBind where

import Control.Monad (when, unless)
import Control.Monad.Identity (Identity(..), runIdentity)
import Control.Monad.Trans.Class (lift)
import qualified Control.Monad.Reader as R
import qualified Control.Monad.Except as E
import qualified Control.Monad.Writer as W
import qualified Control.Monad.State as ST

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Graph as G

import OSC.Expr.Bitraversable
import OSC.Expr.Functors
import OSC.Expr.Comp (Number (..), Ident (..), TNumber (..), Type (..), Op (..))
import qualified OSC.Expr.Comp as C
import qualified OSC.Expr.Base as B
import OSC.Expr.AnnBind

--------------------------------------------------------------------------------

type CaptureM = R.ReaderT (Set Ident) (W.WriterT (Set Ident) (ST.State (Set Ident)))

runCapture :: CaptureM a -> ((a, Set Ident), Set Ident)
runCapture = runIdentity . flip ST.runStateT mempty . W.runWriterT . flip R.runReaderT mempty

markCapturedBindings :: RFunctor f => B.Expr (f B.Expr) -> CaptureM (Expr (f Expr))
markCapturedBindings e = bitraverse (rtraverse markCapturedBindings) (go) e
  where
    go :: RFunctor f => Diff (f B.Expr) -> CaptureM (Expr (f Expr))
    go (DRec t delay param bindings body) = do
      let paramEnv = S.singleton param
      let bindingNames = S.fromList (fmap fst bindings)

      -- Process bindings recursively
      (bindings', capturedByBindings) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (paramEnv <> bindingNames) $ sequence
        [ (n,) <$> rtraverse markCapturedBindings e
        | (n, e) <- bindings
        ]

      -- Process body recursively and capture free vars
      (body', capturedByBody) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (paramEnv <> bindingNames) (rtraverse markCapturedBindings body)

      -- Propagate captures excluding params and bindings
      W.tell ((capturedByBindings <> capturedByBody) S.\\ (paramEnv <> bindingNames))

      -- Accumulate captured bindings
      sequence_
        [ when (S.member captured bindingNames || S.member captured paramEnv) $
            ST.modify (S.singleton captured <>)
        | captured <- S.toList (capturedByBindings <> capturedByBody)
        ]

      pure undefined -- $ Rec t delay param bindings' body'
    go _ = undefined

-- markCapturedBindings :: RFunctor f => f Expr -> CaptureM (f Expr1)
-- markCapturedBindings = rtraverse go
--   where
--     go (Var n) = do
--       env <- R.ask
--       -- Add to captured set if var doesn't reference the params or bindings of the current lambda/rec block
--       unless (S.member n env) $ W.tell (S.singleton n)
--       pure (E_Var n)
-- 
--     go (Lam t params bindings body) = do
--       let paramsEnv = S.fromList params
--       let bindingNames = S.fromList (fmap fst bindings)
-- 
--       -- Process bindings recursively
--       (bindings', capturedByBindings) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (paramsEnv <> bindingNames) $ sequence
--         [ (n,) <$> markCapturedBindings e
--         | (n, e) <- bindings
--         ]
-- 
--       -- Process body recursively and capture free vars
--       (body', capturedByBody) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (paramsEnv <> bindingNames) (markCapturedBindings body)
-- 
--       -- Propagate captures excluding params and bindings
--       W.tell ((capturedByBindings <> capturedByBody) S.\\ (paramsEnv <> bindingNames))
-- 
--       -- Accumulate captured bindings
--       sequence_
--         [ when (S.member captured bindingNames || S.member captured paramsEnv) $
--             ST.modify (S.singleton captured <>)
--         | captured <- S.toList (capturedByBindings <> capturedByBody)
--         ]
-- 
--       pure $ E_Lam t params bindings' body'
-- 
--     go (Rec t delay param bindings body) = do
--       let paramEnv = S.singleton param
--       let bindingNames = S.fromList (fmap fst bindings)
-- 
--       -- Process bindings recursively
--       (bindings', capturedByBindings) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (paramEnv <> bindingNames) $ sequence
--         [ (n,) <$> markCapturedBindings e
--         | (n, e) <- bindings
--         ]
-- 
--       -- Process body recursively and capture free vars
--       (body', capturedByBody) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (paramEnv <> bindingNames) (markCapturedBindings body)
-- 
--       -- Propagate captures excluding params and bindings
--       W.tell ((capturedByBindings <> capturedByBody) S.\\ (paramEnv <> bindingNames))
-- 
--       -- Accumulate captured bindings
--       sequence_
--         [ when (S.member captured bindingNames || S.member captured paramEnv) $
--             ST.modify (S.singleton captured <>)
--         | captured <- S.toList (capturedByBindings <> capturedByBody)
--         ]
-- 
--       pure undefined -- $ Rec t delay param bindings' body'
-- 
--     -- Generic case: recursively process all children
--     go e = bitraverse (rtraverse go) undefined e
