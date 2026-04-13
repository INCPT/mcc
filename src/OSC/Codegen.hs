{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}

module OSC.Codegen where

import Data.Functor.Identity (Identity (runIdentity))
import Data.Bifunctor (first, second)
import Data.Functor.Identity
import Data.List (intercalate, intersperse)
import Data.Data (Data)
import qualified Data.Graph as G
import Data.Map (Map)
import Data.String (IsString)
import qualified Data.Map as M
import Data.Set (Set, (\\))
import qualified Data.Set as S
import Control.Monad.Trans (MonadTrans, lift)
import qualified Control.Monad.Reader as R
import qualified Control.Monad.State.Lazy as ST
import qualified Control.Monad.Trans.Writer.CPS as W
import Prettyprinter
import Prettyprinter.Render.Text (renderStrict)
import qualified Data.Text as T

data TNumber = TI32 | TF32 | TI64 | TF64
  deriving (Eq, Show, Data)

data Type = TNumber TNumber | TArr Type {- length -} Int | TAbs [Type] Type
  deriving (Eq, Show, Data)

sizeOfType :: Type -> Int
sizeOfType (TNumber TI32) = 4
sizeOfType (TNumber TF32) = 4
sizeOfType (TNumber TI64) = 8
sizeOfType (TNumber TF64) = 8
sizeOfType (TArr t dim) = sizeOfType t * dim
sizeOfType (TAbs _ _) = sizeOfType (TNumber TI32) -- TODO PLATFORM: funcref is I32

returnType :: Type -> Type
returnType (TAbs _ t) = t
returnType _ = error "returnType: not an abs"

peelType :: Type -> Type
peelType (TArr t _) = t
peelType (TAbs _ _) = error "peelType: abstraction"
peelType t = error $ "peelType: " <> show t

paramTypes :: String -> Type -> [Type]
paramTypes _ (TAbs params _) = params
paramTypes e _ = error $ "paramTypes: not an abs: " <> e

data Number = I32 Int | I64 Int | F32 Float | F64 Double
  deriving (Show, Data)

numberType :: Number -> Type
numberType (I32 _) = TNumber TI32
numberType (F32 _) = TNumber TF32
numberType (I64 _) = TNumber TI64
numberType (F64 _) = TNumber TF64

newtype Ident = Ident String
  deriving (Eq, Ord, Show, IsString, Data)

data Op = Add | Sub | Mul | Div | Mod | And | Or | Xor | Shl | Shr | Rotl | Rotr 
        | Eq | Ne | Gt | Lt | GEt | LEt 
        | Min | Max | CopySign | Rem
  deriving (Eq, Show, Data)

data UOp = Sqrt | Abs' | Neg | Ceil | Floor | Trunc | Nearest 
         | Clz | Ctz | Popcnt | Eqz
         | Extend | Wrap | Convert | Demote | Promote | Reinterpret
  deriving (Eq, Show)

data Selection lam t sel = Selection (Expr lam sel t) (Expr lam sel t)

data FlatSelection lam t sel
  = FlatSelectionLHS [Expr lam sel t] (Expr lam sel t)
  | FlatSelectionRHS (Expr lam sel t) [Expr lam sel t]

data Lambda sel t lam = Lambda Type {- params -} [Ident] {- bindings -} [(Ident, Expr lam sel t)] {- body -} (Expr lam sel t)

data Mu f = Mu (f (Mu f))

data Expr lam sel t
  = EConst Number
  | EOp t Op (Expr lam sel t) (Expr lam sel t) -- both args and the result are simple types
  | EArr t [Expr lam sel t]

  | EVar t Ident

  -- NOTE: Bindings will be in topsort order after typechecking
  | EAbs Type {- params -} [Ident] {- bindings -} [(Ident, Expr lam sel t)] {- body -} (Expr lam sel t)
  | EAbs2 Type lam

  | EApp t (Expr lam sel t) [Expr lam sel t]

  | ESelect t (Expr lam sel t) {- selector -} (Expr lam sel t)
  | ESelect2 t sel

  -- NOTE: The (return) type of a recursive expression can not contain functions
  -- in order to simplify the logic and not require an initial value. It wouldn't make
  -- much sense generally anyway.

  -- NOTE: Bindings will be in topsort order after typechecking
  | ERec Type {- delay -} Int {- must be of type abstraction -} Ident {- bindings -} [(Ident, Expr lam sel t)] {- body -} (Expr lam sel t)
  deriving (Functor, Show, Data)

type ExprL sel t = Expr (Mu (Lambda sel t)) sel t
type ExprFR sel t = Expr FuncRef sel t

exprType :: Expr lam sel Type -> Type
exprType (EConst n) = numberType n
exprType (EOp t _ _ _) = t
exprType (EArr t _) = t
exprType (EVar t _) = t
exprType (EAbs t _ _ _) = t
exprType (EAbs2 t _) = t
exprType (EApp t _ _) = t
exprType (ESelect t _ _) = t
exprType (ESelect2 t _) = t
exprType (ERec t _ _ _ _) = t

descendExpr :: (Expr lam sel t -> Maybe b) -> Expr lam sel t -> [b]
descendExpr f expr = case f expr of
  Just b -> [b]
  Nothing -> case expr of
    EConst _ -> []
    EOp _ _ a b -> descendExpr f a <> descendExpr f b
    EArr _ exprs -> mconcat (fmap (descendExpr f) exprs)
    EVar _ _ -> []
    EAbs _ _ bindings body -> mconcat (fmap (descendExpr f . snd) bindings) <> descendExpr f body
    EAbs2 _ _ -> []
    EApp _ func args -> descendExpr f func <> mconcat (fmap (descendExpr f) args)
    ESelect _ e idx -> descendExpr f e <> descendExpr f idx
    ESelect2 _ _ -> []
    ERec _ _ _ bindings body -> mconcat (fmap (descendExpr f . snd) bindings) <> descendExpr f body

universeExpr :: (lam -> [Expr lam sel t]) -> (sel -> [Expr lam sel t]) -> Expr lam sel t -> [Expr lam sel t]
universeExpr flam fsel = tailrec (universeExpr flam fsel) . mconcat . descendExpr expr
  where
    expr (EAbs2 _ lam) = Just $ concatMap (universeExpr flam fsel) (flam lam)
    expr (ESelect2 _ sel) = Just $ concatMap (universeExpr flam fsel) (fsel sel)
    expr e = Just [e]

transformExprM
  :: forall lam sel lam' sel' t m. Monad m
  => (lam -> m lam')
  -> (sel -> m sel')
  -> (Expr lam' sel' t -> m (Expr lam' sel' t))
  -> Expr lam sel t
  -> Expr lam' sel' t
transformExprM = undefined

--------------------------------------------------------------------------------

showExpr :: Expr lam sel Type -> String
showExpr = T.unpack . renderStrict . layoutPretty defaultLayoutOptions . ppExpr

showExprL :: Expr lam sel Type -> String
showExprL = T.unpack . renderStrict . layoutPretty defaultLayoutOptions . ppExprL

ppExpr :: Expr lam sel Type -> Doc ann
ppExpr (EConst (I32 n)) = pretty n
ppExpr (EConst (I64 n)) = pretty n
ppExpr (EConst (F32 n)) = pretty n
ppExpr (EConst (F64 n)) = pretty n
ppExpr (EOp _ op a b) = ppOp op a b
ppExpr (EArr _ es) =
  group $ align $ encloseSep lbracket rbracket comma (map ppExpr es)
ppExpr (EVar _ (Ident n)) = pretty n
ppExpr (EAbs t params bs body) =
  vsep
    [ "fn" <> parens (ppParams (paramTypes "ppExpr" t) params) <+> "->" <+> pretty (showType (returnType t))
    , ppAbsBody bs body
    ]
  where
    ppParams [] [] = mempty
    ppParams pts ps = hsep (punctuate comma (zipWith ppParam ps pts))
    ppParam (Ident n) pt = pretty n <> colon <+> pretty (showType pt)
ppExpr (EApp _ f args) = ppApp f args
ppExpr (ESelect _ e idx) = ppSelect e idx
ppExpr (ERec t delay param bs body) =
  vsep
    [ "rec<delay =" <+> pretty delay <> ">" <> parens (ppParam param <> colon <+> pretty (showType t)) <+> "->" <+> pretty (showType t)
    , ppAbsBody bs body
    ]
  where
    ppParam (Ident n) = pretty n

ppOp :: Op -> Expr lam sel Type -> Expr lam sel Type -> Doc ann
ppOp op a b = parens (ppExprInline a <+> pretty (showOp op) <+> ppExprInline b)

ppApp :: Expr lam sel Type -> [Expr lam sel Type] -> Doc ann
ppApp f args = ppFunc f <> parens (hsep (punctuate comma (map ppExprInline args)))
  where
    ppFunc e@(EAbs _ _ _ _) = parens (ppExprInline e)
    ppFunc e@(ERec _ _ _ _ _) = parens (ppExprInline e)
    ppFunc e = ppExprInline e

ppSelect :: Expr lam sel Type -> Expr lam sel Type -> Doc ann
ppSelect e idx = ppExprInline e <> brackets (ppExprInline idx)

ppAbsBody :: [(Ident, Expr lam sel Type)] -> Expr lam sel Type -> Doc ann
ppAbsBody [] body = indent 2 $ "return" <+> ppReturnExpr body
ppAbsBody bindings body = indent 2 $ vsep
  [ vsep [ ppBinding n expr | (n, expr) <- bindings ]
  , mempty
  , "return" <+> ppReturnExpr body
  ]
  where
    ppBinding (Ident n) expr = pretty n <+> "=" <+> ppExprInline expr

ppReturnExpr :: Expr lam sel Type -> Doc ann
ppReturnExpr e@(EAbs _ _ _ _) = ppExprInline e
ppReturnExpr e@(ERec _ _ _ _ _) = ppExprInline e
ppReturnExpr (EOp _ op a b) = ppExprInline a <+> pretty (showOp op) <+> ppExprInline b
ppReturnExpr e = ppExprInline e

ppExprInline :: Expr lam sel Type -> Doc ann
ppExprInline = ppExpr

--------------------------------------------------------------------------------
-- Lisp-like pretty printer

ppExprL :: Expr lam sel Type -> Doc ann
ppExprL (EConst (I32 n)) = pretty n
ppExprL (EConst (I64 n)) = pretty n
ppExprL (EConst (F32 n)) = pretty n
ppExprL (EConst (F64 n)) = pretty n
ppExprL (EOp _ op a b) = parens (ppExprL a <+> pretty (showOp op) <+> ppExprL b)
ppExprL (EArr _ es) = brackets (hsep (punctuate comma (map ppExprL es)))
ppExprL (EVar _ (Ident n)) = pretty n
ppExprL (EAbs t params bs body) =
  if shouldMultiline
    then ppAbsMultiline
    else ppAbsSingleline
  where
    singleLine = T.unpack $ renderStrict $ layoutCompact ppAbsSingleline
    shouldMultiline = length singleLine > 50

    ppAbsSingleline = parens $ "fn" <+> ppParams <> colon <+> ppRetType <+> ppBindingsInline bs <+> ppExprL body
    ppAbsMultiline = parens $ vsep
      [ "fn" <+> ppParams <> colon <+> ppRetType
      , ppBindingsMultiline bs
      , mempty
      , indent 2 (ppExprL body)
      ]

    ppParams = brackets (hsep (punctuate comma (zipWith ppParam params (paramTypes "ppExprL" t))))
    ppParam (Ident n) pt = pretty n <> colon <+> pretty (showType pt)
    ppRetType = pretty (showType (returnType t))

ppExprL (EApp _ f args) = parens (ppExprL f <+> hsep (map ppExprL args))
ppExprL (ESelect _ e idx) = ppExprL e <> brackets (ppExprL idx)
ppExprL (ERec t delay param bs body) =
  if shouldMultiline
    then ppRecMultiline
    else ppRecSingleline
  where
    singleLine = T.unpack $ renderStrict $ layoutCompact ppRecSingleline
    shouldMultiline = length singleLine > 50

    ppRecSingleline = parens $ "rec" <+> ppDelay <+> ppParam <> colon <+> ppRetType <+> ppBindingsInline bs <+> ppExprL body
    ppRecMultiline = parens $ vsep
      [ "rec" <+> ppDelay <+> ppParam <> colon <+> ppRetType
      , ppBindingsMultiline bs
      , mempty
      , indent 2 (ppExprL body)
      ]

    ppDelay = "<delay =" <+> pretty delay <> ">"
    ppParam = brackets (ppParamName <> colon <+> pretty (showType t))
    ppParamName = case param of Ident n -> pretty n
    ppRetType = pretty (showType t)

ppBindingsInline :: [(Ident, Expr lam sel Type)] -> Doc ann
ppBindingsInline [] = "{}"
ppBindingsInline bs = braces (hsep (punctuate comma [ ppBinding n e | (n, e) <- bs ]))
  where
    ppBinding (Ident n) e = pretty n <+> ppExprL e

ppBindingsMultiline :: [(Ident, Expr lam sel Type)] -> Doc ann
ppBindingsMultiline [] = indent 2 "{}"
ppBindingsMultiline bs = indent 2 $ vsep
  [ "{"
  , indent 2 $ vsep [ ppBinding n e | (n, e) <- bs ]
  , "}"
  ]
  where
    ppBinding (Ident n) e = pretty n <+> ppExprL e

--------------------------------------------------------------------------------

type StackM s m a = ST.StateT [s] m a

push :: Monad m => s -> StackM s m ()
push s = ST.modify (s:)

pop :: Monad m => StackM s m (Maybe s)
pop = do
  as <- ST.get
  case as of
    (a:as) -> do
      ST.put as
      pure (Just a)
    _ -> pure Nothing

runStack :: StackM s Identity a -> a
runStack = flip ST.evalState []

--------------------------------------------------------------------------------

-- * TODO: in typechecking, check that static indices are within range
-- ** even better: attach range to index; then check if everything ok in range check
-- ***  otherwise expect a clamp() or wrap() range correcting fun
-- ** if not possible, then demand clamp/wrap in dynamic select index expressions
-- * TODO: in the CallM monad, arguments that get written to the output can pass their array ctx slice to the argument expression, so no need for copy

-- TODO: optimization is performed on the CExpr datatype

-- TODO: alignment in AllocM!

-- TODO: what happens if part of the return value is a capture?
-- this is basically return value ref propagation up the binding chain
-- the most recent returned binding (or argument) gets tagged with "write to return value ref"

newtype FuncRef = FuncRef Int deriving (Eq, Ord, Show)

data AllocRegion = ALocal | AGlobal
  deriving Show

data CIndexable abs
  = CVar Type Ident
  | CApp Type (CExpr abs) [CExpr abs]
  | CRec Type {- delay -} Int {- must be of type abstraction -} {- params -} Ident {- bindings -} [(Ident, AllocRegion, CExpr abs)] (CExpr abs)

data CExpr abs
  = CSel Type [CExpr abs] {- selector -} (CExpr abs)
  | CIndexed [(Type, CExpr abs)] (CIndexable abs) -- selection indices that flow into the inner expression
  | CArr Type [CExpr abs]
  | CConst Number
  | COp Type Op (CExpr abs) (CExpr abs)
  | CAbs Type abs

cexprType :: CExpr abs -> Type
cexprType (CSel t _ _) = t
cexprType (CIndexed idxs expr) = peelOffIndices (length idxs) (indexableType expr)
  where
    peelOffIndices :: Int -> Type -> Type
    peelOffIndices 0 t = t
    peelOffIndices n (TArr t _) = peelOffIndices (n - 1) t
    peelOffIndices _ t = error $ "cexprType: cannot peel " <> show (length idxs) <> " indices from type " <> show t <> " (this is a bug)"
cexprType (CArr t _) = t
cexprType (CConst n) = numberType n
cexprType (COp t _ _ _) = t
cexprType (CAbs t _) = t

indexableType :: CIndexable abs -> Type
indexableType (CVar t _) = t
indexableType (CApp t _ _) = t
indexableType (CRec t _ _ _ _) = t

descendCExpr :: (CIndexable a -> Maybe b) -> (CExpr a -> Maybe b) -> CExpr a -> [b]
descendCExpr fi fe expr = case fe expr of
  Just b -> [b]
  Nothing -> case expr of
    CSel _ choices selector -> mconcat (fmap (descendCExpr fi fe) choices) <> descendCExpr fi fe selector
    CIndexed idxs indexable -> mconcat [ descendCExpr fi fe e | (_, e) <- idxs ] <> descendCIndexable fi fe indexable
    CArr _ exprs -> mconcat (fmap (descendCExpr fi fe) exprs)
    CConst _ -> []
    COp _ _ a b -> descendCExpr fi fe a <> descendCExpr fi fe b
    CAbs _ _ -> []

descendCIndexable :: (CIndexable a -> Maybe b) -> (CExpr a -> Maybe b) -> CIndexable a -> [b]
descendCIndexable fi fe indexable = case fi indexable of
  Just b -> [b]
  Nothing -> case indexable of
    CVar _ _ -> []
    CApp _ f args -> descendCExpr fi fe f <> mconcat (fmap (descendCExpr fi fe) args)
    CRec _ _ _ bindings body -> mconcat [ descendCExpr fi fe e | (_, _, e) <- bindings ] <> descendCExpr fi fe body

tailrec :: (a -> [a]) -> [a] -> [a]
tailrec _ [] = []
tailrec f (h:t) = h:concatMap f t

universeCExpr :: CExpr a -> [CExpr a]
universeCExpr = tailrec universeCExpr . descendCExpr (const Nothing) Just

universeCExprFromIndexable :: CIndexable a -> [CExpr a]
universeCExprFromIndexable = tailrec universeCExpr . descendCIndexable (const Nothing) Just

universeCIndexable :: CExpr a -> [CIndexable a]
universeCIndexable = tailrec universeCIndexableFromIndexable . descendCExpr Just (const Nothing)

universeCIndexableFromIndexable :: CIndexable a -> [CIndexable a]
universeCIndexableFromIndexable = tailrec universeCIndexableFromIndexable . descendCIndexable Just (const Nothing)

transformCExprM :: forall a b m. Monad m => (Type -> a -> m b) -> (CIndexable b -> m (CIndexable b)) -> (CExpr b -> m (CExpr b)) -> CExpr a -> m (CExpr b)
transformCExprM transformAbs transformIndexable transformExpr = go
  where
    go :: CExpr a -> m (CExpr b)
    go expr = case expr of
      CSel t choices selector -> transformExpr =<< (CSel t <$> traverse go choices <*> go selector)
      CIndexed idxs indexable -> transformExpr =<< (CIndexed <$> traverse (\(t, e) -> (t,) <$> go e) idxs <*> goIndexable indexable)
      CArr t exprs -> transformExpr =<< (CArr t <$> traverse go exprs)
      CConst n -> transformExpr (CConst n)
      COp t op a b -> transformExpr =<< (COp t op <$> go a <*> go b)
      CAbs t abs -> transformExpr =<< (CAbs t <$> transformAbs t abs)

    goIndexable :: CIndexable a -> m (CIndexable b)
    goIndexable indexable = case indexable of
      CVar t ident -> transformIndexable (CVar t ident)
      CApp t f args -> transformIndexable =<< (CApp t <$> go f <*> traverse go args)
      CRec t delay param bindings body -> transformIndexable =<< (CRec t delay param <$> traverse (\(n, region, e) -> (n, region,) <$> go e) bindings <*> go body)

transformCExpr :: forall a b. (Type -> a -> b) -> (CIndexable b -> CIndexable b) -> (CExpr b -> CExpr b) -> CExpr a -> CExpr b
transformCExpr f g h expr = runIdentity $ transformCExprM (\t a -> pure (f t a)) (pure . g) (pure . h) expr

--------------------------------------------------------------------------------

showAbs :: Show abs => [Ident] -> [(Ident, AllocRegion, CExpr abs)] -> CExpr abs -> String
showAbs params bs body =
  "λ" <> showParams params <> " " <> showBindings bs <> " = " <> show body
  where
    showParams [] = "()"
    showParams ps = "(" <> intercalate ", " (map (\(Ident n) -> n) ps) <> ")"
  
    showBindings [] = ""
    showBindings bindings = "{ " <> intercalate "; " (map showBinding bindings) <> " }"
    showBinding (Ident n, region, expr) = 
      n <> "@" <> showRegion region <> " = " <> show expr
    showRegion ALocal = "local"
    showRegion AGlobal = "global"

instance Show Abs where
  show (Abs params bs body) = showAbs params bs body

instance Show abs => Show (CIndexable abs) where
  show (CVar _ (Ident n)) = n
  show (CApp _ f a) = show f <> "(" <> intercalate ", " (map show a) <> ")"
  show (CRec t delay param bs body) = "rec[" <> showType t <> ", delay=" <> show delay <> "](" <> showAbs [param] bs body <> ")"

instance Show abs => Show (CExpr abs) where
  show (CSel t cs idx) = 
    "choice[" <> showType t <> "](" <> intercalate " | " (map show cs) <> ")[" <> show idx <> "]"
  show (CIndexed [] expr) = show expr
  show (CIndexed idxs expr) = 
    show expr <> " @ [" <> intercalate ", " (map showIdxPair idxs) <> "]"
    where
      showIdxPair (t, idx) = showType t <> "[" <> show idx <> "]"
  show (CArr t cs) = "[" <> showType t <> ": " <> intercalate ", " (map show cs) <> "]"
  show (CConst n) = show n
  show (COp _ op a b) = "(" <> show a <> " " <> showOp op <> " " <> show b <> ")"
  show (CAbs _ abs) = show abs

showType :: Type -> String
showType (TNumber TI32) = "i32"
showType (TNumber TF32) = "f32"
showType (TNumber TI64) = "i64"
showType (TNumber TF64) = "f64"
showType (TArr t dim) = showType t <> "[" <> show dim <> "]"
showType (TAbs [] retType) = "() -> " <> showType retType
showType (TAbs params retType) = 
  "(" <> intercalate ", " (map showType params) <> ") -> " <> showType retType

showOp :: Op -> String
showOp Add = "+"
showOp Sub = "-"
showOp Mul = "*"
showOp Div = "/"
showOp Mod = "%"
showOp And = "&"
showOp Or = "|"
showOp Xor = "^"
showOp Shl = "<<"
showOp Shr = ">>"
showOp Rotl = "rotl"
showOp Rotr = "rotr"
showOp Eq = "=="
showOp Ne = "!="
showOp Gt = ">"
showOp Lt = "<"
showOp GEt = ">="
showOp LEt = "<="
showOp Min = "min"
showOp Max = "max"
showOp CopySign = "copysign"
showOp Rem = "rem"

--------------------------------------------------------------------------------

toC :: Monad m => CIndexable Abs -> StackM (Type, Expr lam sel Type) m (CExpr Abs)
toC e = do
  idxs <- ST.get
  pure $ CIndexed (map (second toCExpr) idxs) e

-- Pair each index with the appropriate array, so an an expression like
-- `[[0, 1], [2, 3]][1][0]` turns into `[[0, 1][0], [2, 3][0]][1]`.
-- This allows for easy constant index elimination and the generation of more efficient code.
choiceTree :: Monad m => Expr abs sel Type -> StackM (Type, Expr abs sel Type) m (CExpr Abs)
choiceTree (EConst n) = do
  idxs <- ST.get
  pure $ case idxs of
    [] -> CConst n
    _ -> error "choiceTree: cannot index into a constant (this is a bug)"
choiceTree (EOp t op a b) = do
  idxs <- ST.get
  case idxs of
    [] -> pure $ COp t op (toCExpr a) (toCExpr b)
    _ -> error "choiceTree: cannot index into an operation result (this is a bug)"
choiceTree (EVar t n) = toC (CVar t n)
choiceTree (EApp t f as) = toC (CApp t (toCExpr f) (fmap toCExpr as))
choiceTree (EAbs t params bs body) = do
  idxs <- ST.get
  pure $ case idxs of
    [] -> CAbs t (Abs params [ (n, ALocal, toCExpr b) | (n, b) <- bs ] (toCExpr body))
    _ -> error "choiceTree: cannot index into an abstraction (this is a bug)"
choiceTree (ERec t d param bs body) = toC (CRec t d param [ (n, ALocal, toCExpr b) | (n, b) <- bs ] (toCExpr body))
choiceTree (EArr t es) = do
  s <- pop
  case s of
    Just (t, idx) -> do
      es' <- traverse choiceTree es
      push (t, idx)
      pure $ CSel t es' (toCExpr idx)
    Nothing -> pure $ CArr t (map toCExpr es)
choiceTree (ESelect t e idx) = do
  push (t, idx)
  c <- choiceTree e
  _ <- pop
  pure c

--------------------------------------------------------------------------------

-- TODO: this must happen after inlining / CSE (otherwise things like let a = [1, 2, 3] in a[0] won't be optimized)
elimConstIndices :: CExpr Abs -> CExpr Abs
elimConstIndices = transformCExpr (\_ -> id) id go
  where
    go :: CExpr Abs -> CExpr Abs

    -- Eliminate constant index selections by directly selecting the choice
    -- It's ok to prune impure expressions here (since the index is constant those expressions will never be accessible)
    go (CSel _ chs (CConst (I32 idx))) = chs !! idx
    go (CSel _ chs (CConst (I64 idx))) = chs !! idx

    -- Keep everything else as-is
    go ch = ch

optimize :: CExpr Abs -> CExpr Abs
optimize = elimConstIndices

toCExpr :: Expr abs sel Type -> CExpr Abs
toCExpr = optimize . flip ST.evalState [] . choiceTree

--------------------------------------------------------------------------------

newtype Unique a = Unique (ST.State Int a)
  deriving (Functor, Applicative, Monad)

runUnique :: Unique a -> a
runUnique (Unique m) = ST.evalState m 0

fresh :: Unique Ident
fresh = Unique $ do
  n <- ST.get
  ST.put (n + 1)
  pure $ Ident ("_captured_" <> show n)

--------------------------------------------------------------------------------

data Abs = Abs {- params -} [Ident] {- bindings -} [(Ident, AllocRegion, CExpr Abs)] (CExpr Abs)

data Func = Func Type {- params -} [Ident] {- bindings -} [(Ident, AllocRegion, CExpr FuncRef)] (CExpr FuncRef)
  deriving Show

data AbsEnv = AbsEnv
  { funcRefMap :: Map FuncRef Func
  , nextFuncRef :: Int
  } deriving Show

gatherAbstractions :: CExpr Abs -> ST.State AbsEnv (CExpr FuncRef)
gatherAbstractions = transformCExprM transformAbs pure pure
  where
    transformAbs :: Type -> Abs -> ST.State AbsEnv FuncRef
    transformAbs t (Abs params bindings body) = do
      fr <- FuncRef <$> ST.gets (.nextFuncRef)
      ST.modify $ \st -> st { nextFuncRef = st.nextFuncRef + 1 }

      bindings' <- sequenceA [ (n, region,) <$> gatherAbstractions bbody | (n, region, bbody) <- bindings ]
      body' <- gatherAbstractions body

      ST.modify $ \st -> st { funcRefMap = M.insert fr (Func t params bindings' body') st.funcRefMap }
      pure fr

-- | Compute the free variables for each abstraction in the function map.
--
-- Free variables are variables that are referenced but not bound by parameters or bindings.
-- This includes both direct variable references (CVar) and transitive free variables from
-- nested closures (via SFuncRef).
--
-- The computation is recursive: when a function contains a closure (SFuncRef), that closure's
-- free variables are included in the parent function's free variables (unless they're bound
-- by the parent's parameters or bindings). This allows us to track which variables need to
-- be captured across multiple levels of nesting.
--
-- Example:
--   function outer(x) {
--     let y = 1;
--     return function middle(z) {
--       return function inner(w) {
--         return x + y + z + w;  // inner's free vars: {x, y, z}
--       }
--     }
--   }
--
-- Results:
--   - inner's free vars: {x, y, z}
--   - middle's free vars: {x, y} (includes inner's free vars minus middle's params/bindings)
--   - outer's free vars: {} (all variables are bound by outer)

gatherFreeVars :: Map FuncRef Func -> Map FuncRef (Set Ident)
gatherFreeVars funcRefMap = freeVarMap
  where
    freeVarMap :: Map FuncRef (Set Ident)
    freeVarMap = fmap go funcRefMap

    go :: Func -> Set Ident
    go (Func _ params bindings body) = allVars bindings body \\ (S.fromList [ n | (n, _, _) <- bindings ] <> S.fromList params)

    allVars :: [(Ident, AllocRegion, CExpr FuncRef)] -> CExpr FuncRef -> Set Ident
    allVars bindings body = mconcat $ fmap mconcat
      [ [ S.fromList [ n | CVar _ n <- universeCIndexable body ] ]
      , [ S.fromList [ n | (_, _, b) <- bindings, CVar _ n <- universeCIndexable b ] ]

      -- Gather transient free vars (by lazily referencing freeVarMap; this works because no mutual recursion between bindings is allowed)
      , [ fvs | CAbs _ fr <- universeCExpr body, Just fvs <- [ M.lookup fr freeVarMap ] ]
      , [ fvs | (_, _, b) <- bindings, CAbs _ fr <- universeCExpr b, Just fvs <- [ M.lookup fr freeVarMap ] ]
      ]

--------------------------------------------------------------------------------

data GlobalsEnv = GlobalsEnv
  { substMap :: Map FuncRef (Map Ident Ident)
  , globals :: Map Ident Type
  } deriving Show

instance Semigroup GlobalsEnv where GlobalsEnv a b <> GlobalsEnv a' b' = GlobalsEnv (a <> a') (b <> b')
instance Monoid GlobalsEnv where mempty = GlobalsEnv mempty mempty

-- | Transform abstractions to handle captured parameters by creating global bindings.
--
-- This function implements closure conversion for captured parameters. When a nested closure
-- references a parameter from an outer function, we need to make that parameter accessible
-- to the closure. Since the target language (WASM) doesn't support closures natively, we:
--
-- 1. Create a global binding for each captured parameter (e.g., _captured_0 = x)
-- 2. Mark any captured local bindings as global (they keep their original names)
-- 3. Build a substitution map for each closure, mapping original param names to global names
-- 4. Apply substitutions to each closure so it references the global bindings
--
-- Example transformation:
--   function outer(x, y) {
--     let z = 1;
--     return function inner(a) {
--       return x + z + a;  // inner captures param x and binding z
--     }
--   }
--
-- Becomes:
--   function outer(x, y) {
--     global _captured_0 = x;  // New global binding for captured param
--     global z = 1;             // Existing binding marked as global
--     return function inner(a) {
--       return _captured_0 + z + a;  // References substituted
--     }
--   }
--
-- The substitution map tracks: inner -> {x -> _captured_0}
-- Note that z doesn't need substitution since bindings keep their original names.
--
-- Returns:
--   - Updated function map with global bindings and substitutions applied
--   - GlobalsEnv containing the substitution map and global variable types
markCapturedBindings :: Map FuncRef (Set Ident) -> Map FuncRef Func -> Unique (Map FuncRef Func, GlobalsEnv)
markCapturedBindings freeVarMap funcRefMap = do
  (funcRefMapWithGlobalBindings, genv) <- W.runWriterT $ sequenceA (M.mapWithKey go funcRefMap)
  pure (M.mapWithKey (substituteVars genv.substMap) funcRefMapWithGlobalBindings, genv)
  where
    descendFunc :: (CIndexable FuncRef -> Maybe b) -> (CExpr FuncRef -> Maybe b) -> Func -> [b]
    descendFunc fi fe (Func _ _ bindings body) = mconcat
      [ mconcat
          [ descendCExpr fi fe bbody
          | (_, _, bbody) <- bindings
          ]
      , descendCExpr fi fe body
      ]
    
    gatherRecFreeVars :: CExpr FuncRef -> ([(Ident, Type)], Set Ident)
    gatherRecFreeVars expr = mconcat
      [ ((param, t):heads, vars \\ S.singleton param)
      | crec@(CRec t _ param _ _) <- descendCExpr (\e -> case e of crec@(CRec {}) -> Just crec; _ -> Nothing) (const Nothing) expr
      , (heads, vars) <- descendCIndexable gatherVar gatherRec crec
      ]
      where
        gatherVar (CVar _ n) = Just ([], S.singleton n)
        gatherVar _ = Nothing

        gatherRec e@(CIndexed _ (CRec {})) = Just $ gatherRecFreeVars e
        gatherRec _ = Nothing

    -- Process a single function to create global bindings for captured parameters
    go :: FuncRef -> Func -> W.WriterT GlobalsEnv Unique Func
    go funcRef abs@(Func t params bindings body) = do
      -- Find all closures defined in this function and their free variables
      let freeVarsForClosure =
            [ (fr, fvs)
            | fr <- descendFunc (const Nothing) (\e -> case e of CAbs _ fr -> Just fr; _ -> Nothing) abs
            , Just fvs <- [ M.lookup fr freeVarMap ]
            ]

      -- Union of all free variables from nested closures
      let freeVars = mconcat (fmap snd freeVarsForClosure)
      
      -- Find all variables referenced from recursive blocks
      let (recHeads, recFreeVars) = mconcat [ vars | vars <- descendFunc (const Nothing) (Just . gatherRecFreeVars) abs ]

      -- TODO: no need for this after uniquefying all identifiers (+ parameter names)

      -- Create fresh global names for each captured parameter
      capturedParams <- sequence
        [ (ptype, n,) <$> lift fresh
        | (ptype, n) <- zip (paramTypes ("markCapturedBindings: " <> show abs) t) params
        , S.member n freeVars || S.member n recFreeVars
        ]

      -- Build substitution map: original param name -> fresh global name
      let paramSubsts = M.fromList [ (n, subst) | (_, n, subst) <- capturedParams ]
      
      -- Update bindings: mark captured bindings as global, add new global bindings for captured params
      let bindings' = mconcat
            [ [ if S.member n freeVars || S.member n recFreeVars then (n, AGlobal, body) else (n, r, body)
              | (n, r, body) <- bindings
              ]
            , [ (subst, AGlobal, CIndexed [] (CVar t n)) | (t, n, subst) <- capturedParams ]
            ]
      
      -- Record substitutions and global types
      W.tell $ GlobalsEnv
        { substMap = M.fromListWith (<>)
            -- For each closure and each of its free variables that's a captured param,
            -- record the substitution that should be applied to that closure
            [ (fr, M.singleton fv subst)
            | (fr, fvs) <- (funcRef, recFreeVars):freeVarsForClosure
            , fv <- S.toList fvs
            , Just subst <- [ M.lookup fv paramSubsts ]
            ]

        , globals = mconcat
            [ M.fromList [ (n, ptype) | (ptype, _, n) <- capturedParams ]
            , M.fromList [ (n, cexprType e) | (n, AGlobal, e) <- bindings' ]
            ] 
        }

      pure $ Func t params bindings' body

    -- Apply substitutions to a specific function based on its FuncRef
    substituteVars :: Map FuncRef (Map Ident Ident) -> FuncRef -> Func -> Func
    substituteVars frSubstMap fr a@(Func t params bindings body) = case M.lookup fr frSubstMap of
      Just substMap -> Func t params
        (fmap substBinding bindings)
        (transformCExpr (\_ -> id) substVar id body)
        where
          substBinding (n, region, body)
            -- Don't substitute the RHS of captured param bindings (e.g., _captured_0 = x)
            -- We want to keep the original reference to the parameter
            | Just _ <- M.lookup n substMap = (n, region, body)
            | otherwise = (n, region, transformCExpr (\_ -> id) substVar id body)

          substVar :: CIndexable FuncRef -> CIndexable FuncRef
          substVar (CVar t n) = CVar t (M.findWithDefault n n substMap)
          substVar e = e
      _ -> a

--------------------------------------------------------------------------------

-- NOTE: if bindings between two SAbs float collapse them into one
floatExpressions :: Map FuncRef Func -> Map FuncRef Func
floatExpressions = fmap go
  where
    go :: Func -> Func
    go (Func t params bindings body) = undefined

    isPure :: CExpr abs -> CExpr abs
    isPure = undefined

markPureExpressions :: Map FuncRef Func -> Map FuncRef Func
markPureExpressions = fmap go
  where
    go :: Func -> Func
    go (Func t params bindings body) = undefined

    isPure :: CExpr abs -> CExpr abs
    isPure = undefined

-- NEXT
-- * DONE mark captured bindings for storing in global
-- * DONE introduce global bindings for captured arguments, assign argument to them, replace reference to argument with ref to binding in closure
-- * codegen while maintaining focus/select lens
-- * alloc when calling
-- * delay lines (they must have configurable delay); must also be initialized with the initial value
-- * when choice do binary if/elses
-- ** fold the pure part of a computation into the if/else leaves, leaving the impure computations of all parts outside the if/else tree

--------------------------------------------------------------------------------

compileExprs :: Map Ident (CExpr Abs) -> (Map FuncRef (Set Ident), Map Ident (CExpr FuncRef), Map FuncRef Func, GlobalsEnv)
compileExprs toplevelMap = runUnique $ do
  let (toplevelMap', env) = flip ST.runState (AbsEnv mempty 0) $ traverse gatherAbstractions toplevelMap
  let freeVarMap = gatherFreeVars env.funcRefMap

  (funcRefMap, genv) <- markCapturedBindings freeVarMap env.funcRefMap
  
  -- TODO
  let optimize = id

  pure (freeVarMap, toplevelMap', optimize funcRefMap, genv)

compileExpr :: CExpr Abs -> (CExpr FuncRef, Map FuncRef Func, GlobalsEnv)
compileExpr expr = runUnique $ do
  let (expr', env) = flip ST.runState (AbsEnv mempty 0) $ gatherAbstractions expr
  let freeVarMap = gatherFreeVars env.funcRefMap

  (funcRefMap, genv) <- markCapturedBindings freeVarMap env.funcRefMap
  
  -- TODO
  let optimize = id

  pure (expr', optimize funcRefMap, genv)
