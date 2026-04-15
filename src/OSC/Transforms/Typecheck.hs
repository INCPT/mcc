{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module OSC.Transforms.Typecheck where

import Control.Monad.Trans.Class (lift)
import qualified Control.Monad.Reader as R
import qualified Control.Monad.Except as E

import OSC.Expr.Plate (transform)
import OSC.Expr.Functors
import OSC.Expr.TH
import OSC.Expr.Base (TNumber (..), Type (..))
import qualified OSC.Expr.Base as B

$(makeSum "B_" "Exp" [''B.Exp, ''B.Lam, ''B.Select, ''B.Rec])
$(makeBiPlateInstance "B_" ''Exp "B_" ''Exp "" ''Empty)

--------------------------------------------------------------------------------

data TypeError pos = TypeError [pos] String

type ExpA ann = Ann ann Exp
type TypecheckM pos = AnnM pos (E.Except (TypeError pos))

typecheck :: ExpA pos -> TypecheckM pos (ExpA (pos, Type))
typecheck = transform (\(Ann (ann, f)) -> R.local (const ann) (pure f)) f
  where
    f :: Exp (ExpA (pos, Type)) -> TypecheckM pos (ExpA (pos, Type))
    f (B_Const n) = R.ask >>= \pos -> pure $ Ann ((pos, B.numberType n), B_Const n)
    f (B_Op op a@(Ann ((apos, at), _)) b@(Ann ((bpos, bt), _)))
      | at == bt = flowAnn (,at) $ pure $ B_Op op a b
      | otherwise = E.throwError $ TypeError [apos, bpos] undefined
    f _ = undefined
