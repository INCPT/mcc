module OSC.Expr.Comp where

import Data.String (IsString (..))
import Prettyprinter

data TNumber = TI32 | TF32 | TI64 | TF64
  deriving (Eq, Show)

instance Pretty TNumber where
  pretty = \case
    TI32 -> "i32"
    TF32 -> "f32"
    TI64 -> "i64"
    TF64 -> "f64"

data Type = TNumber TNumber | TArr Type {- length -} Int | TLam [Type] Type
  deriving (Eq, Show)

ti32 :: Type
ti32 = TNumber TI32

tf32 :: Type
tf32 = TNumber TF32

ti64 :: Type
ti64 = TNumber TI64

tf64 :: Type
tf64 = TNumber TF64

tarr :: Type -> Int -> Type
tarr = TArr

(-->) :: [Type] -> Type -> Type
(-->) = TLam

(|:) :: Ident -> Type -> (Ident, Type)
(|:) = (,)

instance Pretty Type where
  pretty = \case
    TNumber tn -> pretty tn
    TArr t n -> parens $ hsep ["arr", pretty t, pretty n]
    TLam params ret -> parens $ hsep
      [ "->"
      , parens $ hsep (map pretty params)
      , pretty ret
      ]

sizeOfType :: Type -> Int
sizeOfType (TNumber TI32) = 4
sizeOfType (TNumber TF32) = 4
sizeOfType (TNumber TI64) = 8
sizeOfType (TNumber TF64) = 8
sizeOfType (TArr t dim) = sizeOfType t * dim
sizeOfType (TLam _ _) = sizeOfType (TNumber TI32) -- TODO PLATFORM: funcref is I32

returnType :: Type -> Type
returnType (TLam _ t) = t
returnType _ = error "returnType: not an abs"

peelType :: Type -> Type
peelType (TArr t _) = t
peelType (TLam _ _) = error "peelType: abstraction"
peelType t = error $ "peelType: " <> show t

paramTypes :: String -> Type -> [Type]
paramTypes _ (TLam params _) = params
paramTypes e _ = error $ "paramTypes: not an abs: " <> e

data Number = I32 Int | I64 Int | F32 Float | F64 Double
  deriving Show

instance Pretty Number where
  pretty = \case
    I32 n -> pretty n <> ":i32"
    F32 n -> pretty n <> ":f32"
    I64 n -> pretty n <> ":i64"
    F64 n -> pretty n <> ":f64"

numberType :: Number -> Type
numberType (I32 _) = TNumber TI32
numberType (F32 _) = TNumber TF32
numberType (I64 _) = TNumber TI64
numberType (F64 _) = TNumber TF64

data Ident = Ident String | Captured Int
  deriving (Eq, Ord, Show)

instance IsString Ident where
  fromString = Ident

instance Pretty Ident where
  pretty (Ident name) = pretty name
  pretty (Captured n) = "<captured_" <> pretty n <> ">"

data Op = Add | Sub | Mul | Div | Mod | And | Or | Xor | Shl | Shr | Rotl | Rotr 
        | Eq | Ne | Gt | Lt | GEt | LEt 
        | Min | Max | CopySign | Rem
  deriving (Eq, Show)

instance Pretty Op where
  pretty = \case
    Add -> "+"
    Sub -> "-"
    Mul -> "*"
    Div -> "/"
    Mod -> "mod"
    Rem -> "rem"
    Min -> "min"
    Max -> "max"
    CopySign -> "copysign"
    And -> "and"
    Or -> "or"
    Xor -> "xor"
    Shl -> "shl"
    Shr -> "shr"
    Rotl -> "rotl"
    Rotr -> "rotr"
    Eq -> "="
    Ne -> "!="
    Gt -> ">"
    Lt -> "<"
    GEt -> ">="
    LEt -> "<="

data UOp = Sqrt | Abs | Neg | Ceil | Floor | Trunc | Nearest 
         | Clz | Ctz | Popcnt | Eqz
         | Extend | Wrap | Convert | Demote | Promote | Reinterpret
  deriving (Eq, Show)

instance Pretty UOp where
  pretty = \case
    Sqrt -> "sqrt"
    Abs -> "abs"
    Neg -> "neg"
    Ceil -> "ceil"
    Floor -> "floor"
    Trunc -> "trunc"
    Nearest -> "nearest"
    Clz -> "clz"
    Ctz -> "ctz"
    Popcnt -> "popcnt"
    Eqz -> "eqz"
    Extend -> "extend"
    Wrap -> "wrap"
    Convert -> "convert"
    Demote -> "demote"
    Promote -> "promote"
    Reinterpret -> "reinterpret"

-- Building blocks -------------------------------------------------------------

data Lam exp = Lam Type [Ident] [(Ident, exp)] exp
  deriving (Functor, Foldable, Traversable, Show)

instance Pretty exp => Pretty (Lam exp) where
  pretty (Lam ty params bindings body) = nest 2 $ parens $ vsep
    [ hsep ["lambda", pretty ty]
    , nest 2 $ parens $ hsep ["params", list (map pretty params)]
    , nest 2 $ parens $ vsep
        [ "bindings"
        , nest 2 $ align $ vsep (map prettyBinding bindings)
        ]
    , nest 2 $ vsep ["", nest 2 $ pretty body]
    ]
    where
      list docs = parens $ hsep docs
      prettyBinding (ident, expr) = parens $ hsep [pretty ident, pretty expr]

data Rec exp = Rec Type Int Ident [(Ident, exp)] exp
  deriving (Functor, Foldable, Traversable, Show)

instance Pretty exp => Pretty (Rec exp) where
  pretty (Rec ty delay param bindings body) = nest 2 $ parens $ vsep
    [ hsep ["rec", pretty ty, pretty delay, pretty param]
    , nest 2 $ parens $ nest 2 $ vsep
        [ "bindings"
        , nest 2 $ align $ vsep (map prettyBinding bindings)
        ]
    , nest 2 $ vsep ["", nest 2 $ pretty body]
    ]
    where
      prettyBinding (ident, expr) = parens $ hsep [pretty ident, pretty expr]

data Select exp = Select exp exp
  deriving (Functor, Foldable, Traversable, Show)

instance Pretty exp => Pretty (Select exp) where
  pretty (Select sel idx) = parens $ hsep ["select", pretty sel, pretty idx]

data FoldedSelect exp
  = FoldedSelectL [exp] exp
  | FoldedSelectR exp [exp]
  deriving (Functor, Foldable, Traversable, Show)

instance Pretty exp => Pretty (FoldedSelect exp) where
  pretty = \case
    FoldedSelectL elems idx -> parens $ hsep
      ["folded-select-l", list (map pretty elems), pretty idx]
    FoldedSelectR expr elems -> parens $ hsep
      ["folded-select-r", pretty expr, list (map pretty elems)]
    where
      list docs = parens $ hsep docs

data Expr exp
  = Const Number
  | Arr [exp]
  | Op Op exp exp
  | Var Ident
  | App exp [exp]
  deriving (Functor, Foldable, Traversable, Show)

instance Pretty exp => Pretty (Expr exp) where
  pretty = \case
    Const n -> pretty n
    Arr elems -> parens $ hsep ["arr", list (map pretty elems)]
    Op op a b -> parens $ hsep [pretty op, pretty a, pretty b]
    Var ident -> pretty ident
    App func args -> parens $ hsep ["app", pretty func, list (map pretty args)]
    where
      list docs = parens $ hsep docs

data AllocRegion = AllocLocal | AllocGlobal
  deriving Show

instance Pretty AllocRegion where
  pretty = \case
    AllocLocal -> "<local>"
    AllocGlobal -> "<global>"

data LamAnn exp = LamAnn Type [Ident] [(Ident, AllocRegion, exp)] exp
  deriving (Functor, Foldable, Traversable, Show)

instance Pretty exp => Pretty (LamAnn exp) where
  pretty (LamAnn ty params bindings body) = nest 2 $ parens $ vsep
    [ hsep ["lambda", pretty ty]
    , nest 2 $ parens $ hsep ["params", list (map pretty params)]
    , nest 2 $ parens $ vsep
        [ "bindings"
        , nest 2 $ align $ vsep (map prettyBinding bindings)
        ]
    , nest 2 $ vsep ["", nest 2 $ pretty body]
    ]
    where
      list docs = parens $ hsep docs
      prettyBinding (ident, region, expr) = parens $ hsep
        [pretty ident, pretty region, pretty expr]

data RecAnn exp = RecAnn Type Int Ident [(Ident, AllocRegion, exp)] exp
  deriving (Functor, Foldable, Traversable, Show)

instance Pretty exp => Pretty (RecAnn exp) where
  pretty (RecAnn ty delay param bindings body) = nest 2 $ parens $ vsep
    [ hsep ["rec", pretty ty, pretty delay, pretty param]
    , nest 2 $ parens $ nest 2 $ vsep
        [ "bindings"
        , nest 2 $ align $ vsep (map prettyBinding bindings)
        ]
    , nest 2 $ vsep ["", nest 2 $ pretty body]
    ]
    where
      prettyBinding (ident, region, expr) = parens $ hsep
        [pretty ident, pretty region, pretty expr]

{-
--------------------------------------------------------------------------------

data GatherState = GatherState
  { nextFuncId :: Int
  , collectedFuncs :: [(Int, [String], [(String, Term Sig2)], Term Sig2)]
  } deriving Show

class GatherAlg f where
  gatherAlg :: AlgM (State GatherState) f (Term Sig2)

instance GatherAlg Lam where
  gatherAlg (Lam params locals body) = do
    funcId <- gets nextFuncId
    modify $ \s -> s
      { nextFuncId = nextFuncId s + 1
      , collectedFuncs = (funcId, params, locals, body) : collectedFuncs s
      }
    return $ inject (FuncRef funcId)

instance {-# OVERLAPPABLE #-} (f :<: Sig2) => GatherAlg f where
  gatherAlg = return . inject

instance (GatherAlg f, GatherAlg g) => GatherAlg (f :+: g) where
  gatherAlg (Inl x) = gatherAlg x
  gatherAlg (Inr x) = gatherAlg x

gatherAbs :: Term Sig1 -> Term Sig2
gatherAbs term = evalState (cataM gatherAlg term) initialState
  where
    initialState :: GatherState
    initialState = GatherState
      { nextFuncId = 0
      , collectedFuncs = []
      }
-}
