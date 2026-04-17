{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.AnnBind where

import OSC.Expr.Bitraversable
import OSC.Expr.Comp (Ident, Type)
import OSC.Expr.TH
import qualified OSC.Expr.Comp as C

-- data Lam exp = Lam Type [Ident] [(Ident, exp)] exp

-- data Rec exp = Rec Type Int Ident [(Ident, exp)] exp

$(genSum "" "Expr" [''C.Exp, ''C.Lam, ''C.Select, ''C.Rec])
-- $(genBiPlateInstance "" ''Expr "" ''Expr "" ''Empty)
