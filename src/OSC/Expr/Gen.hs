{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module OSC.Expr.Gen where

import OSC.Ctx

import Test.QuickCheck
import Control.Monad (replicateM)
import Data.List (nub)
import qualified Data.Map as M
import Data.Map (Map)

-- | Generate a random identifier
genIdent :: Gen Ident
genIdent = do
  prefix <- elements ["x", "y", "z", "a", "b", "c", "f", "g"]
  suffix <- choose (0, 99 :: Int)
  return $ Ident (prefix ++ show suffix)

-- | Generate a random type
genType :: Int -> Gen Type
genType depth
  | depth <= 0 = genSimpleType
  | otherwise = frequency
      [ (3, genSimpleType)
      , (1, genArrayType)
      , (1, genFuncType)
      ]
  where
    genSimpleType = TNumber <$> elements [TI32, TF32, TI64, TF64]
    
    genArrayType = do
      elemType <- genType (depth - 1)
      len <- choose (1, 5)
      return $ TArr elemType len
    
    genFuncType = do
      numParams <- choose (0, 3)
      params <- replicateM numParams (genType (depth - 1))
      retType <- genType (depth - 1)
      return $ TAbs params retType

-- | Context for generating expressions with available variables
data GenCtx = GenCtx
  { availableVars :: Map Ident Type
  , maxDepth :: Int
  }

emptyCtx :: GenCtx
emptyCtx = GenCtx M.empty 5

withVar :: Ident -> Type -> GenCtx -> GenCtx
withVar ident t ctx = ctx { availableVars = M.insert ident t (availableVars ctx) }

withVars :: [(Ident, Type)] -> GenCtx -> GenCtx
withVars vars ctx = ctx { availableVars = M.fromList vars <> availableVars ctx }

-- | Generate an expression of a specific type
genExprOfType :: GenCtx -> Type -> Gen (Expr Type)
genExprOfType ctx targetType = sized $ \size ->
  if size <= 0 || maxDepth ctx <= 0
  then genLeaf ctx targetType
  else frequency
    [ (2, genLeaf ctx targetType)
    , (5, genComposite ctx targetType)
    ]

-- | Generate leaf expressions (constants and variables)
genLeaf :: GenCtx -> Type -> Gen (Expr Type)
genLeaf ctx (TNumber TI32) = frequency
  [ (3, EConst . I32 <$> arbitrary)
  , (1, genVarOfType ctx (TNumber TI32))
  ]
genLeaf ctx (TNumber TF32) = frequency
  [ (3, EConst . F32 <$> arbitrary)
  , (1, genVarOfType ctx (TNumber TF32))
  ]
genLeaf ctx (TNumber TI64) = frequency
  [ (3, EConst . I64 <$> arbitrary)
  , (1, genVarOfType ctx (TNumber TI64))
  ]
genLeaf ctx (TNumber TF64) = frequency
  [ (3, EConst . F64 <$> arbitrary)
  , (1, genVarOfType ctx (TNumber TF64))
  ]
genLeaf ctx t@(TArr elemType len) = frequency
  [ (3, genArray ctx elemType len)
  , (1, genVarOfType ctx t)
  ]
genLeaf ctx t@(TAbs _ _) = genVarOfType ctx t

-- | Generate a variable reference of a specific type
genVarOfType :: GenCtx -> Type -> Gen (Expr Type)
genVarOfType ctx targetType = do
  let varsOfType = M.toList $ M.filter (== targetType) (availableVars ctx)
  if null varsOfType
  then genLeaf (ctx { availableVars = M.empty }) targetType
  else do
    (ident, t) <- elements varsOfType
    return $ EVar t ident

-- | Generate composite expressions
genComposite :: GenCtx -> Type -> Gen (Expr Type)
genComposite ctx t@(TNumber tn) = oneof
  [ genBinOp ctx t
  , genSelect ctx t
  , genApp ctx t
  ]
genComposite ctx t@(TArr elemType len) = oneof
  [ genArray ctx elemType len
  , genSelect ctx t
  , genApp ctx t
  ]
genComposite ctx t@(TAbs params retType) = oneof
  [ genAbs ctx params retType
  , genApp ctx t
  ]

-- | Generate a binary operation
genBinOp :: GenCtx -> Type -> Gen (Expr Type)
genBinOp ctx t@(TNumber tn) = do
  op <- elements [Add, Sub, Mul, Div, Mod, And, Or, Xor, Min, Max]
  let ctx' = ctx { maxDepth = maxDepth ctx - 1 }
  a <- scale (`div` 2) $ genExprOfType ctx' t
  b <- scale (`div` 2) $ genExprOfType ctx' t
  return $ EOp t op a b
genBinOp _ t = error $ "genBinOp: not a number type: " ++ show t

-- | Generate an array
genArray :: GenCtx -> Type -> Int -> Gen (Expr Type)
genArray ctx elemType len = do
  let ctx' = ctx { maxDepth = maxDepth ctx - 1 }
  elems <- replicateM len (scale (`div` len) $ genExprOfType ctx' elemType)
  return $ EArr (TArr elemType len) elems

-- | Generate an array selection with in-bounds index
genSelect :: GenCtx -> Type -> Gen (Expr Type)
genSelect ctx targetType = do
  -- Generate an array that contains elements of targetType
  arrLen <- choose (1, 5)
  let arrType = TArr targetType arrLen
  let ctx' = ctx { maxDepth = maxDepth ctx - 1 }
  
  arr <- scale (`div` 2) $ genExprOfType ctx' arrType
  
  -- Generate an in-bounds index (0 to arrLen-1)
  idxVal <- choose (0, arrLen - 1)
  idx <- elements
    [ EConst (I32 idxVal)
    , EConst (I64 idxVal)
    ]
  
  return $ ESelect targetType arr idx

-- | Generate a function application
genApp :: GenCtx -> Type -> Gen (Expr Type)
genApp ctx retType = do
  -- Generate function type
  numParams <- choose (0, 3)
  paramTypes <- replicateM numParams (genType 2)
  let funcType = TAbs paramTypes retType
  
  let ctx' = ctx { maxDepth = maxDepth ctx - 1 }
  
  -- Generate function expression
  func <- scale (`div` 2) $ genExprOfType ctx' funcType
  
  -- Generate arguments of correct types
  args <- mapM (scale (`div` 2) . genExprOfType ctx') paramTypes
  
  return $ EApp retType func args

-- | Generate an abstraction with bindings
genAbs :: GenCtx -> [Type] -> Type -> Gen (Expr Type)
genAbs ctx paramTypes retType = do
  -- Generate parameter names
  paramNames <- replicateM (length paramTypes) genIdent
  let uniqueParams = take (length paramTypes) $ nub paramNames
  let params = zip uniqueParams paramTypes
  
  -- Generate bindings that may reference params and each other (but not recursively)
  numBindings <- choose (0, 3)
  (bindings, bindingCtx) <- genBindings (withVars params ctx) numBindings
  
  -- Generate body that can reference params and bindings
  let bodyCtx = bindingCtx { maxDepth = maxDepth ctx - 1 }
  body <- scale (`div` 2) $ genExprOfType bodyCtx retType
  
  return $ EAbs (TAbs paramTypes retType) uniqueParams bindings body

-- | Generate a list of bindings where each can reference previous ones
genBindings :: GenCtx -> Int -> Gen ([(Ident, Expr Type)], GenCtx)
genBindings ctx 0 = return ([], ctx)
genBindings ctx n = do
  -- Generate a binding
  bindingName <- genIdent
  bindingType <- genType 2
  let ctx' = ctx { maxDepth = maxDepth ctx - 1 }
  bindingExpr <- scale (`div` 2) $ genExprOfType ctx' bindingType
  
  -- Add this binding to context for subsequent bindings
  let newCtx = withVar bindingName bindingType ctx
  
  -- Generate remaining bindings
  (restBindings, finalCtx) <- genBindings newCtx (n - 1)
  
  return ((bindingName, bindingExpr) : restBindings, finalCtx)

-- | Arbitrary instance for Expr Type
instance Arbitrary (Expr Type) where
  arbitrary = do
    targetType <- genType 2
    genExprOfType emptyCtx targetType
  
  shrink (EConst (I32 n)) = [EConst (I32 n') | n' <- shrink n]
  shrink (EConst (I64 n)) = [EConst (I64 n') | n' <- shrink n]
  shrink (EConst (F32 n)) = [EConst (F32 n') | n' <- shrink n]
  shrink (EConst (F64 n)) = [EConst (F64 n') | n' <- shrink n]
  shrink (EOp t _ a b) = [a, b]
  shrink (EArr _ es) = es
  shrink (ESelect _ arr _) = [arr]
  shrink (EApp _ f args) = f : args
  shrink (EAbs _ _ bindings body) = body : map snd bindings
  shrink _ = []
