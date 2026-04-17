{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.Base where

import qualified OSC.Expr.Comp as C

import OSC.Expr.TH

$(genSum "" "Expr" [''C.Exp, ''C.Lam, ''C.Select, ''C.Rec])
$(genSmartConstructors ''Expr)
