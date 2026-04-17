{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.AnnBind where

import OSC.Expr.Comp (Ident, Type)
import OSC.Expr.TH
import qualified OSC.Expr.Base as B
import qualified OSC.Expr.Comp as C

data AllocRegion = Local | Global
  deriving Show

data LamAnn exp = LamAnn_ Type [Ident] [(Ident, AllocRegion, exp)] exp
data RecAnn exp = RecAnn_ Type Int Ident [(Ident, AllocRegion, exp)] exp

$(genSum "" "Expr" [''C.Exp, ''C.Select, ''LamAnn, ''RecAnn])

$(genDiff "D" "Diff" "" ''B.Expr "" ''Expr)

$(genBitraversableInstance "" ''B.Expr "" ''Expr "D" ''Diff)