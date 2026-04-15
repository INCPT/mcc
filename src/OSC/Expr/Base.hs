{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.Base 
  ( module OSC.Expr.Base
  , module OSC.Expr.Pretty
  ) where

import OSC.Expr.TH
import OSC.Expr.Pretty
import qualified OSC.Expr.Comp as C

$(genSum "" "Expr" [''C.Exp, ''C.Lam, ''C.Select, ''C.Rec])
$(genPlateInstance ''Expr)
$(genSmartConstructors ''Expr)
