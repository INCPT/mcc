{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RecursiveDo #-}

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
import OSC.Expr.AnnBind hiding (const)

--------------------------------------------------------------------------------

type CaptureM = R.ReaderT (Map Ident Ident, Map Ident Ident) (W.WriterT (Set Ident) (ST.State Int))

capture :: Ident -> (Maybe Ident -> a) -> CaptureM a
capture n f = do
  (_, env) <- R.ask
  
  case M.lookup n env of
    Just subst -> do
      W.tell (S.singleton n)
      pure $ f (Just subst)
    Nothing -> pure $ f Nothing

withSubsts :: [Ident] -> CaptureM a -> CaptureM (a, Ident -> Maybe Ident)
withSubsts names f = do
  (prev, env) <- R.ask

  substs <- fmap M.fromList $ sequence [ (n,) <$> nextName | n <- names ]

  -- Process f and capture free vars
  (a, captured) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (substs, prev <> env) f

  -- Propagate captures excluding params and bindings
  W.tell (captured S.\\ S.fromList names)

  pure (a, \n -> if S.member n captured then M.lookup n substs else Nothing)
  where
    nextName = do
      n <- ST.state $ \n -> (n, n + 1)
      pure $ Captured n

annCapturedBindings_ :: Ann Type SRC.Expr -> CaptureM (Ann Type Expr)
annCapturedBindings_ = bitraverse (rtraverse . trav) diff
  where
    nextName = do
      n <- ST.state $ \n -> (n, n + 1)
      pure $ Captured n
    
    trav _ (SRC.PVar n) = capture n $ \subst -> case subst of
      Just subst -> PVar subst
      Nothing -> PVar n
    trav rmap e = rmap e

    diff :: Diff (Ann Type SRC.Expr) -> CaptureM (Expr (Ann Type Expr))
    diff (PLam typ params bindings body) = do
      ((bindings', body'), lkupSubst) <- withSubsts (params <> fmap fst bindings) $ do
        bindings' <- sequenceA [ (n,) <$> annCapturedBindings_ bbody | (n, bbody) <- bindings ]
        body' <- annCapturedBindings_ body
        pure (bindings', body')

      let bindings'' = mconcat
            [ [ case lkupSubst n of
                  Just n' -> (n', C.AllocGlobal, Ann (t, e))
                  Nothing -> (n, C.AllocLocal, Ann (t, e))
              | (n, Ann (t, e)) <- bindings'
              ]
            , [ (paramSubst, C.AllocGlobal, Ann (t, Expr $ C.Var p))
              | (p, t) <- zip params (paramTypes ("markCapturedBindings: " <> show typ) typ)
              , Just paramSubst <- [ lkupSubst p ]
              ]
            ]

      pure $ PLamAnn typ params bindings'' body'
   
    diff (PRec typ delay param bindings body) = do
      ((bindings', body'), lkupSubst) <- withSubsts (param : fmap fst bindings) $ do
        bindings' <- sequenceA [ (n,) <$> annCapturedBindings_ bbody | (n, bbody) <- bindings ]
        body' <- annCapturedBindings_ body
        pure (bindings', body')

      let paramSubst = case lkupSubst param of
            Just subst -> subst
            Nothing -> param

      let bindings'' =
            [ case lkupSubst n of
                Just n' -> (n', C.AllocGlobal, Ann (t, e))
                Nothing -> (n, C.AllocLocal, Ann (t, e))
            | (n, Ann (t, e)) <- bindings'
            ]
   
      pure $ PRecAnn typ delay paramSubst bindings'' body'

annCapturedBindings :: Ann Type SRC.Expr -> Ann Type Expr
annCapturedBindings = fst . flip ST.evalState 0 . W.runWriterT . flip R.runReaderT mempty . annCapturedBindings_

--------------------------------------------------------------------------------

type PureM = R.Reader (Map Ident Pure)

annPure_ :: Ann a Expr -> PureM (Ann (a, Pure) Expr)
annPure_ ann@(Ann (a, expr)) = case expr of
    PConst n -> pure $ Ann ((a, Pure), PConst n)

    PLamAnn typ params bindings body -> do
      env <- R.ask
      mdo
        let bindingEnv = env <> M.fromList [ (n, snd $ fst $ unAnn e') | (n, _, e') <- bindings' ]
        bindings' <- sequence
          [ do
              e' <- R.local (const bindingEnv) (annPure_ e)
              pure (n, region, e')
          | (n, region, e) <- bindings
          ]
        body' <- R.local (const bindingEnv) (annPure_ body)
        
        let p = extract [ e' | (_, _, e') <- bindings' ] <> extract [body']
        pure $ Ann ((a, p), PLamAnn typ params bindings' body')

    PRecAnn typ delay param bindings body -> do
      env <- R.ask
      mdo
        let bindingEnv = env <> M.fromList [ (n, snd $ fst $ unAnn e') | (n, _, e') <- bindings' ]
        bindings' <- sequence
          [ do
              e' <- R.local (const bindingEnv) (annPure_ e)
              pure (n, region, e')
          | (n, region, e) <- bindings
          ]
        body' <- R.local (const bindingEnv) (annPure_ body)
        
        -- RecAnn is always impure
        pure $ Ann ((a, Impure), PRecAnn typ delay param bindings' body')

    PVar ident -> do
      env <- R.ask
      let p = M.findWithDefault Pure ident env
      pure $ Ann ((a, p), PVar ident)
    
    -- Generic case: use tupAnnM-like traversal
    _ -> tupAnnM annPure_ ann
  where
    extract :: [Ann (a, Pure) Expr] -> Pure
    extract = foldMap (snd . fst . unAnn)

annPure :: Ann a Expr -> Ann (a, Pure) Expr
annPure expr = flip R.runReader mempty $ annPure_ expr
