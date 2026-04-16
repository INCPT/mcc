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

$(genSum "E_" "Expr1" [''C.Exp, ''C.Lam, ''C.Select])

instance TraversableBi Expr Expr1 Empty
