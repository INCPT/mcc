{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module OSC.Expr.THTest where

import qualified Control.Monad.Reader as R
import qualified Control.Monad.State as ST

import Data.Functor.Identity
import qualified Data.Map as M

import OSC.Expr.TH

-- Simple recursive functor (can be paired with Identity)
newtype Mu f = Mu { unMu :: f (Mu f) }

-- Annotated recursive functor + monad
newtype Ann ann f = Ann { unAnn :: (ann, f (Ann ann f)) }
type AnnM ann = R.Reader ann

hoistAnn :: Functor f => (ann -> ann') -> Ann ann f -> Ann ann' f
hoistAnn h (Ann (ann, f)) = Ann (h ann, fmap (hoistAnn h) f)

hoistAnnM :: Traversable f => Monad m => (ann -> m ann') -> Ann ann f -> m (Ann ann' f)
hoistAnnM h (Ann (ann, f)) = Ann <$> ((,) <$> h ann <*> traverse (hoistAnnM h) f)

flowAnn :: (ann -> ann') -> AnnM ann (exp (Ann ann' exp)) -> AnnM ann (Ann ann' exp)
flowAnn f m = R.ask >>= \ann -> Ann <$> (f ann,) <$> m

-- DAG recursive functor + monad
data Dag k f = Node (f (Dag k f)) | Key k
type DagM k expr = R.Reader (k -> expr (Dag k expr))

-- write a TH function that:

---- having the following types

data Value exp = Const Int | Arr [exp]
data Expr exp = Single | Add exp exp | Mul (Maybe (Either String [exp])) exp | Exp (Maybe (Maybe (Maybe exp))) (Maybe exp) (Maybe (Maybe exp))
data Lambda exp = Lambda String [(String, exp)] exp
data FuncRef exp = FuncRef Int
data Empty exp

$(makeSum "S1_" "Sum1" [''Value, ''Expr, ''FuncRef])
$(makeSum "S2_" "Sum2" [''Value, ''Expr, ''Lambda])
$(makeSum "S3_" "Sum3" [''Value, ''Expr])

-- $(makePlateInstance ''Sum1)
-- $(makePlateInstance ''Sum2)

$(makeDiff "D1_" "Diff1" "S1_" ''Sum1 "" ''Value)
$(makeDiff "D2_" "Diff2" "S2_" ''Sum2 "S1_" ''Sum1)
$(makeDiff "D3_" "Diff3" "S2_" ''Sum2 "S3_" ''Sum3)

$(makeBiPlateInstance "S1_" ''Sum1 "" ''Value "D1_" ''Diff1)
$(makeBiPlateInstance "S2_" ''Sum2 "S1_" ''Sum1 "D2_" ''Diff2)
$(makeBiPlateInstance "S2_" ''Sum2 "S3_" ''Sum3 "D3_" ''Diff3)
$(makeBiPlateInstance "S2_" ''Sum2 "S2_" ''Sum2 "" ''Empty)

sum2 :: Mu Sum2
sum2 = undefined

test :: Identity (Mu Sum1)
test = transformBi (pure . unMu) (pure . Mu) go sum2
  where
    go :: Diff2 (Mu Sum1) -> Identity (Mu Sum1)
    go (D2_Lambda n bindings body) = pure $ Mu $ S1_FuncRef 5

type FuncM = ST.State (Int, M.Map Int (String, [(String, Dag Int Sum3)], Dag Int Sum3))

test2 :: FuncM (Dag Int Sum3)
test2 = transformBi (pure . unMu) (pure . Node) go sum2
  where
    go :: Diff3 (Dag Int Sum3) -> FuncM (Dag Int Sum3)
    go (D3_Lambda n bindings body) = do
      nextId <- ST.state $ \(nextId, funcMap) -> (nextId, (nextId + 1, M.insert nextId (n, bindings, body) funcMap))
      pure $ Key nextId

data SourcePos

data Type = TNumber | TArr [Type] | TAbs [Type] Type
  deriving Eq

type ASum2 ann = Ann ann Sum2

sum2' :: Ann pos Sum2
sum2' = undefined

test3 :: AnnM pos (ASum2 (pos, Type))
test3 = transformBi (\(Ann (ann, f)) -> R.local (const ann) (pure f)) wrap go sum2'
  where
    wrap :: Sum2 (ASum2 (pos, Type)) -> AnnM pos (ASum2 (pos, Type))
    wrap (S2_Const n) = R.ask >>= \pos -> pure $ Ann ((pos, TNumber), S2_Const n)
    wrap (S2_Add a@(Ann ((_, at), _)) b@(Ann ((_, bt), _)))
      | at == bt = flowAnn (,at) $ pure $ S2_Add a b
    wrap _ = undefined

    go = undefined
    -- go :: Empty (ASum2 (SourcePos, Type)) -> AnnM SourcePos (ASum2 (SourcePos, Type))
    -- go _ = undefined

-- instance BiPlate Sum1 Value Diff1 where
--   transformBi unwrap wrap f expr = do
--     inner <- unwrap expr
--     case inner of
--       S1_Const n -> wrap =<< (Const <$> pure n)
--       S1_Arr as  -> wrap =<< (Arr <$> traverse (transformBi unwrap wrap f) as)
-- 
--       S1_Single ->  f =<< pure D1_Single
--       S1_Add a b -> f =<< (D1_Add <$> (traverse (transformBi unwrap wrap f)) a <*> transformBi unwrap wrap f b)
--       S1_Mul a b -> f =<< (D1_Mul <$> (traverse (traverse (traverse (transformBi unwrap wrap f)))) a <*> transformBi unwrap wrap f b)
--       _ -> undefined

-- instance Plate Sum1 where
--   descend unwrap extract expr = do
--     inner <- unwrap expr
--     a <- extract inner
--     case a of
--       Just a' -> pure [a']
--       Nothing -> case inner of
--         S1_Const _ -> pure []
--         S1_Arr exprs -> (foldMapM (descend unwrap extract)) (F.toList exprs)
--         S1_Add exp1 exp2 -> (<>) <$> (foldMapM (descend unwrap extract)) (F.toList exp1) <*> descend unwrap extract exp2
--         S1_Mul exp1 exp2 -> (<>) <$> (foldMapM (descend unwrap extract)) (foldList $ F.toList $ foldList $ F.toList exp1) <*> descend unwrap extract exp2
--         S1_Exp exp1 -> (foldMapM (descend unwrap extract)) (foldList $ F.toList $ foldList $ F.toList exp1)
--         _ -> undefined

-- $(do
--   decs <- makePlateInstance ''Sum1
--   reportWarning (pprint decs)
--   pure decs
--  )

{-

---- and calling

------ makeSum "S_" "Sum0" [''Value, ''Expr]

---- will generate the following datatype:

data Sum0 exp
  = S_Const Int
  | S_Arr [exp]
  | S_Add exp exp
  | S_Mul exp exp
  deriving (Functor, Foldable, Traversable)

---- and implement the Plate and Biplate classes:

instance Plate Sum0 where
  descend unwrap extract expr = do
    inner <- unwrap expr
    a <- extract inner
    case a of
      Just a' -> pure [a']
      Nothing -> case inner of
        S_Const _ -> pure []
        -- if field is of type `h (g (f exp)) ...` (like `[exp]` or `[Maybe exp]`) then just traverse (and figure out how to do nested traversls) - we'll throw a type error if f isn't a Traversable
        S_Arr exprs -> fmap mconcat $ traverse (descend unwrap extract) exprs
        S_Add exp1 exp2 -> (<>) <$> descend unwrap extract exp1 <*> descend unwrap extract exp2
        S_Mul exp1 exp2 -> (<>) <$> descend unwrap extract exp1 <*> descend unwrap extract exp2

instance BiPlate Sum0 Sum0 Sum0 where
  transformBi unwrap wrap f expr = do
    inner <- unwrap expr
    case inner of
      S_Const n   -> wrap =<< pure (S_Const n)
      S_Arr exprs -> wrap =<< f =<< (S_Arr <$> traverse (transformBi unwrap wrap f) exprs)
      S_Add a b   -> wrap =<< f =<< (S_Add <$> transformBi unwrap wrap f a <*> transformBi unwrap wrap f b)
      S_Mul a b   -> wrap =<< f =<< (S_Add <$> transformBi unwrap wrap f a <*> transformBi unwrap wrap f b)
  
---- calling

------ makeDiff "D_" "Diff_Sum0_Expr" ''Sum0 ''Value

---- will generate the following datatype:

data Diff_Sum0_Expr exp
  = D_Add exp exp
  | D_Mul exp exp

---- and implement the following BiPlate class:

instance BiPlate Sum0 Value Diff_Sum0_Expr where
  transformBi unwrap wrap f expr = do
    inner <- unwrap expr
    case inner of
      S_Const n -> wrap =<< (Const <$> n)
      S_Arr as  -> wrap =<< (Arr <$> traverse (transformBi unwrap wrap f) as)

      S_Add a b -> wrap =<< f =<< (D_Add <$> transformBi unwrap wrap f a <*> transformBi unwrap wrap f b)
      S_Mul a b -> wrap =<< f =<< (D_Add <$> transformBi unwrap wrap f a <*> transformBi unwrap wrap f b)

-}
