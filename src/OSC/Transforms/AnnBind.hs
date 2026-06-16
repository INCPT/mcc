{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeOperators #-}

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
import OSC.Expr.Comp (Ident (..), Captured (..), Type, paramTypes)
import qualified OSC.Expr.FoldSel as SRC
import qualified OSC.Expr.Comp as C
import OSC.Expr.AnnBind hiding (const)

import OSC.Records
import GHC.Records (HasField)

--------------------------------------------------------------------------------

type CaptureM = R.ReaderT (Map Ident Ident, Map Ident Ident) (W.WriterT (Set Ident) (ST.State Int))

--------------------------------------------------------------------------------

type RenameM = R.ReaderT (M.Map Ident Captured) (W.WriterT (Set Captured) (ST.State Int))

annCapturedBindings_ :: Ann Type SRC.Expr -> RenameM (Ann Type Expr)
annCapturedBindings_ = bitraverse rtraverse diff
  where
    nextName (Ident orig) = do
      n <- ST.state $ \n -> (n, n + 1)
      pure $ Captured orig n

    diff :: Diff (Ann Type SRC.Expr) -> RenameM (Expr (Ann Type Expr))
    diff (PIVar n) = R.ask >>= \env -> do
      let cpt = env M.! n
      W.tell $ S.singleton cpt
      pure $ PCVar cpt

    diff (PLam typ params bindings body) = do
      env <- R.ask

      cptParams <- sequence [ (n,) <$> nextName n | n <- params ]
      cptBindings <- sequence [ (n,) <$> nextName n | (n, _) <- bindings ]

      let cptMap = M.fromList (cptParams <> cptBindings)
      let cptSet = S.fromList (M.elems cptMap)

      ((bindings', body'), captured) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (cptMap <> env) $ do
        bindings' <- sequence [ (n,) <$> annCapturedBindings_ bbody | ((_, bbody), (_, n)) <- zip bindings cptBindings ]
        body' <- annCapturedBindings_ body
        pure (bindings', body')

      W.tell (captured S.\\ cptSet)

      let bindings'' =
            [ if S.member n captured
                then (n, C.AllocGlobal, Ann (t, e))
                else (n, C.AllocLocal, Ann (t, e))
            | (n, Ann (t, e)) <- bindings'
            ]
      let params' =
            [ if S.member p captured
                then (p, C.AllocGlobal)
                else (p, C.AllocLocal)
            | (_, p) <- cptParams
            ]

      pure $ PLamAnn typ params' bindings'' body'

    diff (PRec typ delay param bindings body) = do
      env <- R.ask

      cptParam <- nextName param
      cptBindings <- sequence [ (n,) <$> nextName n | (n, _) <- bindings ]

      let cptMap = M.fromList ((param, cptParam):cptBindings)
      let cptSet = S.fromList (M.elems cptMap)

      ((bindings', body'), captured) <- lift $ lift $ W.runWriterT $ flip R.runReaderT (cptMap <> env) $ do
        bindings' <- sequence [ (n,) <$> annCapturedBindings_ bbody | ((_, bbody), (_, n)) <- zip bindings cptBindings ]
        body' <- annCapturedBindings_ body
        pure (bindings', body')

      W.tell (captured S.\\ cptSet)

      let bindings'' =
            [ if S.member n captured
                then (n, C.AllocGlobal, Ann (t, e))
                else (n, C.AllocLocal, Ann (t, e))
            | (n, Ann (t, e)) <- bindings'
            ]

      pure $ PRecAnn typ delay cptParam bindings'' body'

annCapturedBindings :: Ann Type SRC.Expr -> Ann Type Expr
annCapturedBindings = fst . flip ST.evalState 0 . W.runWriterT . flip R.runReaderT mempty . annCapturedBindings_

--------------------------------------------------------------------------------

type PureM = R.Reader (Map Ident Pure)

-- TODO: arrays which are written to by the imperative code must be marked as impure too

{-

annPure_ :: Extend "pure" Pure r r' => AnnR r Expr -> PureM (AnnR r' Expr)
annPure_ ann@(Ann (r, expr)) = case expr of
    PConst n -> pure $ Ann (Pure ~> r, PConst n)

    PLamAnn typ params bindings body -> mdo
      let bindingsEnv = M.fromList [ (n, (fst $ unAnn e').pure) | (n, _, e') <- bindings' ]
      bindings' <- sequence
        [ do
            e' <- R.local (bindingsEnv <>) (annPure_ e)
            pure (n, region, e')
        | (n, region, e) <- bindings
        ]
      body' <- R.local (bindingsEnv <>) (annPure_ body)
      
      let p = extract [ e' | (_, _, e') <- bindings' ] <> extract [body']
      pure $ Ann (p ~> r, PLamAnn typ params bindings' body')

    PRecAnn typ delay param bindings body -> mdo
      let bindingsEnv = M.fromList [ (n, (fst $ unAnn e').pure) | (n, _, e') <- bindings' ]
      bindings' <- sequence
        [ do
            e' <- R.local (bindingsEnv <>) (annPure_ e)
            pure (n, region, e')
        | (n, region, e) <- bindings
        ]
      body' <- R.local (bindingsEnv <>) (annPure_ body)
      
      -- RecAnn is always impure
      pure $ Ann (Impure ~> r, PRecAnn typ delay param bindings' body')

    PCVar ident -> do
      env <- R.ask
      let p = M.findWithDefault Pure ident env
      pure $ Ann (p ~> r, PCVar ident)
    
    -- Generic case: use recAnnM-like traversal
    _ -> recAnnM #pure annPure_ ann
  where
    (~>) :: Extend "pure" Pure r r' => Pure -> Record r -> Record r'
    p ~> r = extend #pure p r

    extract :: HasField "pure" r Pure => [Ann r Expr] -> Pure
    extract = foldMap ((.pure) . fst . unAnn)

annPure :: Extend "pure" Pure r r' => AnnR r Expr -> AnnR r' Expr
annPure expr = flip R.runReader mempty $ annPure_ expr

-}

--------------------------------------------------------------------------------

-- Float pure expressions to the topmost lambda abstractions that contains them.

-- This must happen after inlining and dead code elim, since then it is guaranteed that
-- any pure expression in a nested lambda abstraction will be evaluated more than once
-- because the inliner will have inlined functions that are called only once, and the dead
-- code elim will have discarded bindings that are not used at all.

type FloatM = ST.State ()

floatPureExprs :: f Expr -> FloatM (f Expr)
floatPureExprs = undefined
