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
  deriving (Eq, Ord)

instance Monoid Pure where
  mempty = Pure

instance Semigroup Pure where
  Pure <> Pure = Pure
  _ <> _ = Impure

type PureM = R.Reader (Map Ident Pure)

annPure :: Ann a Expr -> Ann (a, Pure) Expr
annPure expr = flip R.runReader mempty $ annPure_ expr

annPure_ :: Ann a Expr -> PureM (Ann (a, Pure) Expr)
annPure_ = pileM' purity
  where
    pileM' :: (Traversable f, Monad m) => (f (Ann a f) -> m (b, f (Ann (a, b) f))) -> Ann a f -> m (Ann (a, b) f)
    pileM' f (Ann (a, e)) = do
      (b, e') <- f e
      pure $ Ann ((a, b), e')

    extract :: [Ann (a, Pure) Expr] -> Pure
    extract = foldMap (snd . fst . unAnn)

    purity :: Expr (Ann a Expr) -> PureM (Pure, Expr (Ann (a, Pure) Expr))
    purity (PConst n) = pure (Pure, PConst n)
    
    purity (PArr elems) = do
      elems' <- traverse annPure_ elems
      pure (extract elems', PArr elems')
    
    purity (PFoldedSelectL elems idx) = do
      elems' <- traverse annPure_ elems
      idx' <- annPure_ idx
      pure (extract (idx':elems'), PFoldedSelectL elems' idx')
    
    purity (PFoldedSelectR expr elems) = do
      expr' <- annPure_ expr
      elems' <- traverse annPure_ elems
      pure (extract (expr':elems'), PFoldedSelectR expr' elems')
    
    purity (PLamAnn typ params bindings body) = do
      -- Process bindings with mdo to allow forward references
      env <- R.ask
      let processBindings = do
            bindings' <- sequence
              [ do
                  e' <- R.local (const bindingEnv) (annPure_ e)
                  pure (n, region, e')
              | (n, region, e) <- bindings
              ]
            let bindingEnv = env <> M.fromList [ (n, snd $ fst $ unAnn e') | (n, _, e') <- bindings' ]
            pure (bindings', bindingEnv)
      
      (bindings', bindingEnv) <- processBindings
      body' <- R.local (const bindingEnv) (annPure_ body)
      
      let p = extract [ e' | (_, _, e') <- bindings' ] <> extract [body']
      pure (p, PLamAnn typ params bindings' body')
    
    purity (PRecAnn typ delay param bindings body) = do
      -- RecAnn is always impure, but we still need to process subexpressions
      env <- R.ask
      let processBindings = do
            bindings' <- sequence
              [ do
                  e' <- R.local (const bindingEnv) (annPure_ e)
                  pure (n, region, e')
              | (n, region, e) <- bindings
              ]
            let bindingEnv = env <> M.fromList [ (n, snd $ fst $ unAnn e') | (n, _, e') <- bindings' ]
            pure (bindings', bindingEnv)
      
      (bindings', bindingEnv) <- processBindings
      body' <- R.local (const bindingEnv) (annPure_ body)
      
      pure (Impure, PRecAnn typ delay param bindings' body')
    
    purity (POp op lhs rhs) = do
      lhs' <- annPure_ lhs
      rhs' <- annPure_ rhs
      pure (extract [lhs', rhs'], POp op lhs' rhs')
    
    purity (PVar ident) = do
      env <- R.ask
      let p = M.findWithDefault Pure ident env
      pure (p, PVar ident)
    
    purity (PApp func args) = do
      func' <- annPure_ func
      args' <- traverse annPure_ args
      pure (extract (func':args'), PApp func' args')
