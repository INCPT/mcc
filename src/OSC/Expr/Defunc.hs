{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.Defunc where

import OSC.Expr.Comp (FuncRef)
import OSC.Expr.TH
import qualified OSC.Expr.AnnBind as SRC
import qualified OSC.Expr.Comp as C

import Prettyprinter
import OSC.Pretty

import GHC.Generics

data Expr exp
  = Expr (C.Expr exp)
  | FoldedSelect (C.FoldedSelect exp)
  | RecAnn (C.RecAnn exp)
  | FuncRef FuncRef
 deriving (Functor, Foldable, Traversable, Generic, Show)

$(genPatternSynonyms "P" ''Expr)
$(genSmartConstructors ''Expr)

instance Pretty exp => Pretty (Expr exp) where
  pretty = genPretty

data Diff exp
  = LamAnn (C.LamAnn exp)

$(genPatternSynonyms "P" ''Diff)
$(genBitraversableInstance ''SRC.Expr ''Expr ''Diff)
