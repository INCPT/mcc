{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.Defunc where

import qualified Data.Map as M

import qualified OSC.Expr.AnnBind as SRC
import OSC.Expr.Comp (Ident)
import qualified OSC.Expr.Comp as C
import OSC.Expr.TH

import Prettyprinter
import OSC.Pretty

import GHC.Generics

newtype FuncRef = FuncRef Int
  deriving (Eq, Ord, Show)

instance Pretty FuncRef where
  pretty (FuncRef fr) = "fr:" <> pretty fr

data Expr exp
  = Expr (C.Expr exp)
  | FoldedSelect (C.FoldedSelect exp)
  | Rec Ident
  | Func FuncRef
 deriving (Functor, Foldable, Traversable, Generic, Show)

$(genPatternSynonyms "P" ''Expr)
$(genSmartConstructors ''Expr)

instance Pretty exp => Pretty (Expr exp) where
  pretty = genPretty

data Diff exp
  = LamAnn (C.LamAnn exp)
  | RecAnn (C.RecAnn exp)

$(genPatternSynonyms "P" ''Diff)
$(genBitraversableInstance ''SRC.Expr ''Expr ''Diff)

data DefuncMap f = DefuncMap
  { funcMap :: M.Map FuncRef (C.LamAnn (f Expr))
  , recs :: [C.RecAnn (f Expr)]
  }
