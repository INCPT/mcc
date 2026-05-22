{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.Base where

import qualified OSC.Expr.Comp as C

import OSC.Expr.TH

import Prettyprinter
import OSC.Pretty

import GHC.Generics

data Expr exp
  = BExpr (C.Expr exp)
  | BSelect (C.Select exp)
  | BVar (C.IVar exp)
  | BLam (C.Lam exp)
  | BRec (C.Rec exp)
  deriving (Eq, Functor, Foldable, Traversable, Generic, Show)

$(genSmartConstructors ''Expr)
$(genPatternSynonyms (('P':)) ''Expr)

instance Pretty exp => Pretty (Expr exp) where
  pretty = genPretty
