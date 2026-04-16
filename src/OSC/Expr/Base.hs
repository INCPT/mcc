{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.Base where

import OSC.Expr.TH
import OSC.Expr.Plate
import qualified OSC.Expr.Comp as C

$(genSum "" "Expr" [''C.Exp, ''C.Lam, ''C.Select, ''C.Rec])
$(genSmartConstructors ''Expr)
$(genBiPlateInstance "" ''Expr "" ''Expr "" ''Empty)
$(genBitraversableInstance "" ''Expr "" ''Expr "" ''Empty)

$(genSum "E_" "Expr1" [''C.Exp, ''C.Lam, ''C.Select])
$(genDiff "D" "Diff" "" ''Expr "E_" ''Expr1)

$(genBitraversableInstance "" ''Expr "E_" ''Expr1 "D" ''Diff)

-- instance TraversableBi Expr Expr1 Empty
