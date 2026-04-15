{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.Base where

import OSC.Expr.TH
import qualified OSC.Expr.Comp as C

$(genSum "" "Expr" [''C.Exp, ''C.Lam, ''C.Select, ''C.Rec])
$(genPlateInstance ''Expr)
$(genSmartConstructors ''Expr)