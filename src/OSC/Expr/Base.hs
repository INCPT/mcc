{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module OSC.Expr.Base where

import Data.String (IsString)

data TNumber = TI32 | TF32 | TI64 | TF64
  deriving (Eq, Show)

data Type = TNumber TNumber | TArr Type {- length -} Int | TAbs [Type] Type
  deriving (Eq, Show)

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
  deriving Show

numberType :: Number -> Type
numberType (I32 _) = TNumber TI32
numberType (F32 _) = TNumber TF32
numberType (I64 _) = TNumber TI64
numberType (F64 _) = TNumber TF64

newtype Ident = Ident String
  deriving (Eq, Ord, Show, IsString)

data Op = Add | Sub | Mul | Div | Mod | And | Or | Xor | Shl | Shr | Rotl | Rotr 
        | Eq | Ne | Gt | Lt | GEt | LEt 
        | Min | Max | CopySign | Rem
  deriving (Eq, Show)

data UOp = Sqrt | Abs | Neg | Ceil | Floor | Trunc | Nearest 
         | Clz | Ctz | Popcnt | Eqz
         | Extend | Wrap | Convert | Demote | Promote | Reinterpret
  deriving (Eq, Show)

--------------------------------------------------------------------------------

data Lam exp = Lam [Ident] [(Ident, exp)] exp

data Rec exp = Rec Ident [(Ident, exp)] exp

data Select exp = Select exp exp

data FoldedSelect exp
  = FoldedSelectL [exp] exp
  | FoldedSelectR exp [exp]

data Exp exp
  = Const Number
  | Arr [exp]
  | Op Op exp exp
  | Var Ident
  | App exp [exp]

--------------------------------------------------------------------------------

{-
type FoldSelectionsM = Stack (Type, Term Sig0) (Term Sig1)

foldSelections :: Term Sig0 -> Term Sig1
foldSelections = runStack . expr
  where
    rhs :: Term Sig1 -> FoldSelectionsM
    rhs expr = do
      idxs <- ST.get
      case idxs of
        [] -> pure expr
        _ -> pure $ inject $ FoldedSelectR expr (fmap (foldSelections . snd) idxs)

    expr :: Term Sig0 -> FoldSelectionsM
    expr term = case project term of
      -- Handle Value constructors
      Just (Const n) -> rhs $ inject (Const n)
      Just (Arr es) -> do
        s <- pop
        case s of
          Just (t, idx) -> do
            es' <- traverse expr es
            push (t, idx)
            pure $ inject $ FoldedSelectL es' (foldSelections idx)
          Nothing -> pure $ inject $ Arr (fmap foldSelections es)
      
      -- Handle Exp constructors
      Nothing -> case project term of
        Just (Op a b) -> rhs $ inject $ Op (foldSelections a) (foldSelections b)
        Just (Var n) -> rhs $ inject $ Var n
        Just (App f args) -> rhs $ inject $ App (foldSelections f) (fmap foldSelections args)
        
        -- Handle Lam constructor
        Nothing -> case project term of
          Just (Lam params locals body) -> 
            rhs $ inject $ Lam params (fmap (fmap foldSelections) locals) (foldSelections body)
          
          -- Handle Select constructor
          Nothing -> case project term of
            Just (Select sel idx) -> do
              push (exprType term, idx)
              sel' <- expr sel
              _ <- pop
              pure sel'
            Nothing -> error "foldSelections: unknown constructor"

    exprType :: Term Sig0 -> Type
    exprType term = case project term of
      Just (Const _) -> TNumber TI32  -- Assuming constants are I32
      Just (Arr es) -> case es of
        [] -> error "exprType: empty array"
        (e:_) -> TArr (exprType e) (length es)
      Nothing -> case project term of
        Just (Op _ _) -> TNumber TI32  -- Assuming ops return I32
        Just (Var _) -> error "exprType: cannot determine type of variable"
        Just (App _ _) -> error "exprType: cannot determine type of application"
        Nothing -> case project term of
          Just (Lam _ _ _) -> error "exprType: cannot determine type of lambda"
          Nothing -> case project term of
            Just (Select e _) -> peelType (exprType e)
            Nothing -> error "exprType: unknown constructor"
    
    peelType :: Type -> Type
    peelType (TArr t _) = t
    peelType t = error $ "peelType: cannot peel type " ++ show t

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