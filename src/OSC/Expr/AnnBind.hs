{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.AnnBind where

import Data.Text (Text)
import qualified Data.Text as T

import OSC.Expr.Bitraversable
import OSC.Expr.Comp (Ident(..), Number(..), Op(..), Type(..), TNumber(..))
import OSC.Expr.Functors
import OSC.Expr.TH
import qualified OSC.Expr.Base as B
import qualified OSC.Expr.Comp as C

import Prettyprinter
import Prettyprinter.Render.Text

data Expr exp
  = Expr (C.Expr exp)
  | Select (C.Select exp)
  | LamAnn (C.LamAnn exp)
  | RecAnn (C.RecAnn exp)
  deriving (Functor, Foldable, Traversable, Show)

pattern PLamAnn a b c d = LamAnn (C.LamAnn a b c d) 

-- $(genSmartConstructors ''Expr)

data Diff exp
  = Lam (C.Lam exp)
  | Rec (C.Rec exp)

pattern PConst n = Expr (C.Const n) 
pattern PVar n = Expr (C.Var n) 

pattern PLam a b c d = Lam (C.Lam a b c d) 
pattern PRec a b c d e = Rec (C.Rec a b c d e) 

{-# COMPLETE PLam, PRec #-}

-- lamAnn :: Type -> [Ident] -> [(Ident, C.AllocRegion, exp)] -> exp -> Expr exp
-- lamAnn a b c d = LamAnn $ C.LamAnn a b c d

lamAnnR :: Corecursive f => Type -> [Ident] -> [(Ident, C.AllocRegion, f Expr)] -> f Expr -> f Expr
lamAnnR a b c d = embed $ LamAnn $ C.LamAnn a b c d

instance Bitraversable B.Expr Expr Diff where
  bitraverse trav f = trav go
    where
        go (B.Expr v) = Expr <$> traverse (trav go) v
        go (B.Select v) = Select <$> traverse (trav go) v

        go (B.Lam v) = f (Lam v)
        go (B.Rec v) = f (Rec v)

-- -- | Pretty print a Fix Expr as an S-expression
-- prettySexp :: Fix Expr -> Doc ann
-- prettySexp = go
--   where
--     go (Fix expr) = case expr of
--       Const n -> prettyNumber n
--       
--       Op op a b -> parens $ hsep
--         [ prettyOp op
--         , go a
--         , go b
--         ]
--       
--       Arr elems -> parens $ hsep
--         [ "arr"
--         , list (map go elems)
--         ]
--       
--       Var (Ident name) -> pretty name
--       
--       LamAnn ty params bindings body -> nest 2 $ parens $ vsep
--         [ hsep ["lambda", prettyType ty]
--         , nest 2 $ parens $ hsep ["params" , list (map prettyIdent params)]
--         , nest 2 $ parens $ vsep
--             [ "bindings"
--             , nest 2 $ align $ vsep (map prettyBinding bindings)
--             ]
--         , nest 2 $ vsep ["", nest 2 $ go body]
--         ]
--       
--       App func args -> parens $ hsep
--         [ "app"
--         , go func
--         , list (map go args)
--         ]
--       
--       Select sel idx -> parens $ hsep
--         [ "select"
--         , go sel
--         , go idx
--         ]
--       
--       RecAnn ty delay param bindings body -> nest 2 $ parens $ vsep
--         [ hsep ["rec", prettyType ty, pretty delay, prettyIdent param]
--         , nest 2 $ parens $ nest 2 $ vsep
--             [ "bindings"
--             , nest 2 $ align $ vsep (map prettyBinding bindings)
--             ]
--         , nest 2 $ vsep ["", nest 2 $ go body]
--         ]
--     
--     prettyBinding (ident, region, expr) = parens $ hsep
--       [ prettyIdent ident
--       , case region of
--           Local -> "<local>"
--           Global -> "<global>"
--       , go expr
--       ]
--     
--     list docs = parens $ hsep docs
--     
--     prettyIdent (Ident name) = pretty name
-- 
-- prettyNumber :: Number -> Doc ann
-- prettyNumber = \case
--   I32 n -> pretty n <> ":i32"
--   F32 n -> pretty n <> ":f32"
--   I64 n -> pretty n <> ":i64"
--   F64 n -> pretty n <> ":f64"
-- 
-- prettyOp :: Op -> Doc ann
-- prettyOp = \case
--   Add -> "+"
--   Sub -> "-"
--   Mul -> "*"
--   Div -> "/"
--   Mod -> "mod"
--   Rem -> "rem"
--   Min -> "min"
--   Max -> "max"
--   CopySign -> "copysign"
--   And -> "and"
--   Or -> "or"
--   Xor -> "xor"
--   Shl -> "shl"
--   Shr -> "shr"
--   Rotl -> "rotl"
--   Rotr -> "rotr"
--   Eq -> "="
--   Ne -> "!="
--   Gt -> ">"
--   Lt -> "<"
--   GEt -> ">="
--   LEt -> "<="
-- 
-- prettyType :: Type -> Doc ann
-- prettyType = \case
--   TNumber tn -> prettyTNumber tn
--   TArr t n -> parens $ hsep ["arr", prettyType t, pretty n]
--   TLam params ret -> parens $ hsep
--     [ "->"
--     , parens $ hsep (map prettyType params)
--     , prettyType ret
--     ]
-- 
-- prettyTNumber :: TNumber -> Doc ann
-- prettyTNumber = \case
--   TI32 -> "i32"
--   TF32 -> "f32"
--   TI64 -> "i64"
--   TF64 -> "f64"
-- 
-- -- | Render to Text with default layout options
-- renderSexp :: Fix Expr -> Text
-- renderSexp = renderStrict . layoutPretty defaultLayoutOptions . prettySexp
-- 
-- -- | Render to String with default layout options
-- showSexp :: Fix Expr -> String
-- showSexp = T.unpack . renderSexp
