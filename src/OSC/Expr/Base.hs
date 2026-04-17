{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.Base where

import qualified OSC.Expr.Comp as C

import OSC.Expr.TH

$(genSum "" "Expr" [''C.Exp, ''C.Lam, ''C.Select, ''C.Rec])
$(genSmartConstructors ''Expr)

$(genSum "E_" "Expr1" [''C.Exp, ''C.Lam, ''C.Select])
$(genDiff "D" "Diff" "" ''Expr "E_" ''Expr1)

$(genBitraversableInstance "" ''Expr "E_" ''Expr1 "D" ''Diff)
