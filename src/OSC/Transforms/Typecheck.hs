{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Transforms.Typecheck where

import OSC.Expr.TH
import OSC.Expr.Base

$(makeSum "B_" "Exp" [''Exp, ''Lam, ''Select])