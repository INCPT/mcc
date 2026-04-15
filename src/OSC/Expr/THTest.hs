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

data Mu f = Mu (f (Mu f))

-- write a TH function that:

---- having the following types

data Value exp = Const exp Int | Arr [exp]
data Expr exp = Single | Add (Maybe exp) exp | Mul (Maybe (Either String [exp])) exp exp | Exp (Maybe (Maybe (Maybe exp)))
data Lambda exp = Lambda String [(String, exp)] exp

$(makeSum "S1_" "Sum1" [''Value, ''Expr])
$(makeSum "S2_" "Sum2" [''Value, ''Expr, ''Lambda])

$(makePlateInstance ''Sum1)
$(makePlateInstance ''Sum2)

$(makeDiff "D1_" "Diff1" ''Sum1 ''Value)
$(makeDiff "D2_" "Diff2" ''Sum2 ''Sum1)

-- instance Plate Sum1 where
--   descend unwrap extract expr = do
--     inner <- unwrap expr
--     a <- extract inner
--     case a of
--       Just a' -> pure [a']
--       Nothing -> case inner of
--         S_Const _ -> pure []
--         S_Arr exprs -> (fmap mconcat . traverse (descend unwrap extract)) (F.toList exprs)
--         S_Add exp1 exp2 -> (<>) <$> (fmap mconcat . traverse (descend unwrap extract)) (F.toList exp1) <*> descend unwrap extract exp2
--         S_Mul exp1 exp2 -> (<>) <$> (fmap mconcat . traverse (descend unwrap extract)) (mconcat $ F.toList $ sequenceA $ F.toList exp1) <*> descend unwrap extract exp2
--         S_Exp exp1 -> (fmap mconcat . traverse (descend unwrap extract)) (mconcat $ F.toList $ sequenceA $ F.toList $ mconcat $ F.toList $ sequenceA $ F.toList exp1)

-- $(do
--   decs <- makePlateInstance ''Sum1
--   reportWarning (pprint decs)
--   pure decs
--  )

bla :: Mu Sum1 -> Mu Sum1
bla (Mu (S1_Const a n)) = Mu (S1_Const a n)
bla _ = undefined

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
      S_Const n -> wrap =<< pure (Const n)
      S_Arr as  -> wrap =<< (Arr <$> traverse (transformBi unwrap wrap f) as)

      S_Add a b -> wrap =<< f =<< (D_Add <$> transformBi unwrap wrap f a <*> transformBi unwrap wrap f b)
      S_Mul a b -> wrap =<< f =<< (D_Add <$> transformBi unwrap wrap f a <*> transformBi unwrap wrap f b)

-}
