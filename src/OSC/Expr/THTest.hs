{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.THTest where

import Data.Functor.Identity
import qualified Data.Foldable as F

import OSC.Expr.TH

{-
-- Simple recursive functor (can be paired with Identity)
data Mu f = Mu (f (Mu f))

-- Annotated recursive functor + monad
data Ann ann f = Ann (ann, f (Ann ann f))
data AnnM ann expr a = AnnM (Ann ann expr -> a)

-- DAG recursive functor + monad
data Dag k f = Node (f (Dag k f)) | Key k
data DagM k expr a = DagM ((k -> expr (Dag k expr)) -> a)
-}

data Mu f = Mu { unmu :: f (Mu f) }

-- write a TH function that:

---- having the following types

data Value exp = Const Int | Arr [exp]
data Expr exp = Single | Add (Maybe exp) exp | Mul (Maybe (Either String [exp])) exp | Exp (Maybe (Maybe (Maybe exp))) (Maybe exp) (Maybe (Maybe exp))
data Lambda exp = Lambda String [(String, exp)] exp
data FuncRef exp = FuncRef Int

$(makeSum "S1_" "Sum1" [''Value, ''Expr, ''FuncRef])
$(makeSum "S2_" "Sum2" [''Value, ''Expr, ''Lambda])

$(makePlateInstance ''Sum1)
$(makePlateInstance ''Sum2)

$(makeDiff "D1_" "Diff1" "S1_" ''Sum1 "" ''Value)
$(makeDiff "D2_" "Diff2" "S2_" ''Sum2 "S1_" ''Sum1)

$(makeBiPlateInstance "S1_" ''Sum1 "" ''Value "D1_S1_" ''Diff1)
$(makeBiPlateInstance "S2_" ''Sum2 "S1_" ''Sum1 "D2_S2_" ''Diff2)

sum2 :: Mu Sum2
sum2 = undefined

test :: Identity (Mu Sum1)
test = transformBi (pure . unmu) (pure . Mu) go sum2
  where
    go :: Diff2 (Mu Sum1) -> Identity (Sum1 (Mu Sum1))
    go (D2_S2_Lambda n bindings body) = pure $ S1_FuncRef 5

-- instance BiPlate Sum1 Value Diff1 where
--   transformBi unwrap wrap f expr = do
--     inner <- unwrap expr
--     case inner of
--       S1_Const n -> wrap =<< (Const <$> pure n)
--       S1_Single -> wrap =<< f =<< pure D1_S1_Single
--       S1_Arr as  -> wrap =<< (Arr <$> traverse (transformBi unwrap wrap f) as)
-- 
--       S1_Add a b -> wrap =<< f =<< (D1_S1_Add <$> (traverse (transformBi unwrap wrap f)) a <*> transformBi unwrap wrap f b)
--       S1_Mul a b -> wrap =<< f =<< (D1_S1_Mul <$> (traverse (traverse (traverse (transformBi unwrap wrap f)))) a <*> transformBi unwrap wrap f b)
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
