{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.AnnBind where

import OSC.Expr.TH
import qualified OSC.Expr.Base as SRC
import qualified OSC.Expr.Comp as C

import Prettyprinter
import OSC.Pretty

import GHC.Generics

data Expr exp
  = Expr (C.Expr exp)
  | Select (C.Select exp)
  | LamAnn (C.LamAnn exp)
  | RecAnn (C.RecAnn exp)
 deriving (Functor, Foldable, Traversable, Generic, Show)

$(genPatternSynonyms "P" ''Expr)
$(genSmartConstructors ''Expr)

instance Pretty exp => Pretty (Expr exp) where
  pretty = genPretty

data Diff exp
  = Lam (C.Lam exp)
  | Rec (C.Rec exp)

$(genPatternSynonyms "P" ''Diff)
$(genBitraversableInstance ''SRC.Expr ''Expr ''Diff)
