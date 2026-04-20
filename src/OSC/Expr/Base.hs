{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.Base where

import qualified OSC.Expr.Comp as C

import OSC.Expr.TH

data Expr exp
  = Expr (C.Expr exp)
  | Lam (C.Lam exp)
  | Select (C.Select exp)
  | Rec (C.Rec exp)
  deriving (Functor, Foldable, Traversable, Show)

$(genSmartConstructors ''Expr)
$(genPatternSynonyms ''Expr)
