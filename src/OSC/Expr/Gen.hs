{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module OSC.Expr.Gen where

import OSC.Ctx
import OSC.Expr

import Test.QuickCheck
import Control.Monad (replicateM)
import qualified Data.Map as M
import Data.Map (Map)

-- | Generate a random identifier
genIdent :: Gen Ident
genIdent = do
  prefix <- elements ["x", "y", "z", "a", "b", "c", "f", "g"]
  suffix <- choose (0, 999 :: Int)
  pure $ Ident (prefix <> show suffix)

-- | Generate n unique identifiers
genUniqueIdents :: Int -> Gen [Ident]
genUniqueIdents n = go n []
  where
    go 0 acc = pure acc
    go remaining acc = do
      ident <- genIdent
      if ident `elem` acc
        then go remaining acc  -- Try again if duplicate
        else go (remaining - 1) (ident : acc)

-- | Generate a unique identifier not in the given list
genUniqueIdentNotIn :: [Ident] -> Gen Ident
genUniqueIdentNotIn existing = do
  ident <- genIdent
  if ident `elem` existing
    then genUniqueIdentNotIn existing  -- Try again if duplicate
    else pure ident

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
      pure $ TArr elemType len
    
    genFuncType = do
      numParams <- choose (0, 3)
      params <- replicateM numParams (genType (depth - 1))
      retType <- genType (depth - 1)
      pure $ TAbs params retType

-- | Generate a type that doesn't contain functions (for ERec)
genNonFuncType :: Int -> Gen Type
genNonFuncType depth
  | depth <= 0 = genSimpleType
  | otherwise = frequency
      [ (3, genSimpleType)
      , (1, genArrayType)
      ]
  where
    genSimpleType = TNumber <$> elements [TI32, TF32, TI64, TF64]
    
    genArrayType = do
      elemType <- genNonFuncType (depth - 1)
      len <- choose (1, 5)
      pure $ TArr elemType len

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
genLeaf ctx (TNumber TI32) = case genVarOfType ctx (TNumber TI32) of
  Just varGen -> frequency [(3, EConst . I32 <$> arbitrary), (1, varGen)]
  Nothing -> EConst . I32 <$> arbitrary
genLeaf ctx (TNumber TF32) = case genVarOfType ctx (TNumber TF32) of
  Just varGen -> frequency [(3, EConst . F32 <$> arbitrary), (1, varGen)]
  Nothing -> EConst . F32 <$> arbitrary
genLeaf ctx (TNumber TI64) = case genVarOfType ctx (TNumber TI64) of
  Just varGen -> frequency [(3, EConst . I64 <$> arbitrary), (1, varGen)]
  Nothing -> EConst . I64 <$> arbitrary
genLeaf ctx (TNumber TF64) = case genVarOfType ctx (TNumber TF64) of
  Just varGen -> frequency [(3, EConst . F64 <$> arbitrary), (1, varGen)]
  Nothing -> EConst . F64 <$> arbitrary
genLeaf ctx t@(TArr elemType len) = case genVarOfType ctx t of
  Just varGen -> frequency [(3, genArray ctx elemType len), (1, varGen)]
  Nothing -> genArray ctx elemType len
genLeaf ctx t@(TAbs _ _) = case genVarOfType ctx t of
  Just varGen -> varGen
  Nothing -> genAbs ctx (paramTypes t) (returnType t)

-- | Generate a variable reference of a specific type (returns Nothing if no vars available)
genVarOfType :: GenCtx -> Type -> Maybe (Gen (Expr Type))
genVarOfType ctx targetType =
  if null varsOfType
    then Nothing
    else Just $ do
      (ident, t) <- elements varsOfType
      pure $ EVar t ident
  where
    varsOfType = M.toList $ M.filter (== targetType) (availableVars ctx)

-- | Generate composite expressions
genComposite :: GenCtx -> Type -> Gen (Expr Type)
genComposite ctx t@(TNumber tn) = oneof
  [ genBinOp ctx t
  , genSelect ctx t
  , genApp ctx t
  , genRec ctx t
  ]
genComposite ctx t@(TArr elemType len) = oneof
  [ genArray ctx elemType len
  , genSelect ctx t
  , genApp ctx t
  , genRec ctx t
  ]
genComposite ctx t@(TAbs params retType) = oneof
  [ genAbs ctx params retType
  , genApp ctx t
  ]

-- | Generate a binary operation
genBinOp :: GenCtx -> Type -> Gen(Expr Type)
genBinOp ctx t@(TNumber tn) = do
  op <- elements [Add, Sub, Mul, And, Or, Xor, Min, Max]

  a <- scale (`div` 2) $ genExprOfType ctx' t
  b <- scale (`div` 2) $ genExprOfType ctx' t

  pure $ EOp t op a b
  where
    ctx' = ctx { maxDepth = maxDepth ctx - 1 }
genBinOp _ t = error $ "genBinOp: not a number type: " ++ show t

-- | Generate an array
genArray :: GenCtx -> Type -> Int -> Gen (Expr Type)
genArray ctx elemType len = do
  elems <- replicateM len (scale (`div` len) $ genExprOfType ctx' elemType)
  pure $ EArr (TArr elemType len) elems
  where
    ctx' = ctx { maxDepth = maxDepth ctx - 1 }

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
  
  pure $ ESelect targetType arr idx

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
  
  pure $ EApp retType func args

-- | Generate an abstraction with bindings
genAbs :: GenCtx -> [Type] -> Type -> Gen (Expr Type)
genAbs ctx paramTypes retType = do
  -- Generate unique parameter names
  paramNames <- genUniqueIdents (length paramTypes)
  let params = zip paramNames paramTypes
  
  -- Generate bindings that may reference params and each other (but not recursively)
  numBindings <- choose (0, 3)
  (bindings, bindingCtx) <- genBindings (withVars params ctx) numBindings
  
  -- Generate body that can reference params and bindings
  let bodyCtx = bindingCtx { maxDepth = maxDepth ctx - 1 }
  body <- scale (`div` 2) $ genExprOfType bodyCtx retType
  
  pure $ EAbs (TAbs paramTypes retType) paramNames bindings body

-- | Generate a list of bindings where each can reference previous ones
genBindings :: GenCtx -> Int -> Gen ([(Ident, Expr Type)], GenCtx)
genBindings ctx 0 = pure ([], ctx)
genBindings ctx n = do
  -- Generate a unique binding name (not already in context)
  bindingName <- genUniqueIdentNotIn (M.keys $ availableVars ctx)
  bindingType <- genType 2
  let ctx' = ctx { maxDepth = maxDepth ctx - 1 }
  bindingExpr <- scale (`div` 2) $ genExprOfType ctx' bindingType
  
  -- Add this binding to context for subsequent bindings
  let newCtx = withVar bindingName bindingType ctx
  
  -- Generate remaining bindings
  (restBindings, finalCtx) <- genBindings newCtx (n - 1)
  
  pure ((bindingName, bindingExpr) : restBindings, finalCtx)

-- | Generate a recursive expression (ERec)
-- The type cannot contain functions, and the recursive parameter represents
-- the previous value in the recursive computation
genRec :: GenCtx -> Type -> Gen (Expr Type)
genRec ctx recType = do
  -- Generate delay (number of samples to delay)
  delay <- choose (1, 5)
  
  -- Generate unique recursive parameter name
  paramName <- genUniqueIdentNotIn (M.keys $ availableVars ctx)
  let paramCtx = withVar paramName recType ctx
  
  -- Generate bindings that can reference the recursive parameter
  numBindings <- choose (0, 3)
  (bindings, bindingCtx) <- genBindings paramCtx numBindings
  
  -- Generate body that MUST use the recursive parameter
  let bodyCtx = bindingCtx { maxDepth = maxDepth ctx - 1 }
  body <- scale (`div` 2) $ genBodyUsingParam bodyCtx recType paramName
  
  pure $ ERec recType delay paramName bindings body
  where

    -- Generate a body expression that uses the recursive parameter
    genBodyUsingParam :: GenCtx -> Type -> Ident -> Gen (Expr Type)
    genBodyUsingParam ctx t@(TNumber tn) paramName = oneof
      [ -- Binary operation with the recursive parameter
        do
          op <- elements [Add, Sub]
          other <- scale (`div` 2) $ genExprOfType ctx t
          -- Randomly put param on left or right
          elements
            [ EOp t op (EVar t paramName) other
            , EOp t op other (EVar t paramName)
            ]
      , -- Use param in a more complex expression
        do
          op1 <- elements [Add, Sub]
          op2 <- elements [Add, Sub]
          a <- scale (`div` 3) $ genExprOfType ctx t
          b <- scale (`div` 3) $ genExprOfType ctx t
          pure $ EOp t op1 (EOp t op2 (EVar t paramName) a) b
      ]
    genBodyUsingParam ctx t@(TArr elemType len) paramName = oneof
      [ -- Select from the recursive parameter array
        do
          idxVal <- choose (0, len - 1)
          idx <- elements [EConst (I32 idxVal), EConst (I64 idxVal)]
          pure $ ESelect elemType (EVar t paramName) idx
      , -- Build array using recursive parameter elements
        do
          indices <- replicateM len $ choose (0, len - 1)
          elems <- mapM mkSelect indices
          pure $ EArr t elems
      , -- Combine recursive param with other values in array
        do
          idxVal <- choose (0, len - 1)
          idx <- elements [EConst (I32 idxVal), EConst (I64 idxVal)]
          otherElems <- replicateM (len - 1) (scale (`div` len) $ genExprOfType ctx elemType)
          pos <- choose (0, len - 1)
          let (before, after) = splitAt pos otherElems
          let paramElem = ESelect elemType (EVar t paramName) idx
          pure $ EArr t (before <> [paramElem] <> after)
      ]
      where
        mkSelect i = do
          idx <- elements [EConst (I32 i), EConst (I64 i)]
          pure $ ESelect elemType (EVar t paramName) idx
    genBodyUsingParam ctx t paramName = 
      -- Fallback: just return the parameter itself
      pure $ EVar t paramName

-- | Arbitrary instance for Expr Type
instance Arbitrary (Expr Type) where
  arbitrary = do
    returnType <- genType 2
    genExprOfType emptyCtx (TAbs [] returnType)
  
  shrink (EConst (I32 n)) = [EConst (I32 n') | n' <- shrink n]
  shrink (EConst (I64 n)) = [EConst (I64 n') | n' <- shrink n]
  shrink (EConst (F32 n)) = [EConst (F32 n') | n' <- shrink n]
  shrink (EConst (F64 n)) = [EConst (F64 n') | n' <- shrink n]
  shrink (EOp t _ a b) = [a, b]
  shrink (EArr _ es) = es
  shrink (ESelect _ arr _) = [arr]
  shrink (EApp _ f args) = f : args
  shrink (EAbs _ _ bindings body) = body : map snd bindings
  shrink (ERec _ _ _ bindings body) = body : map snd bindings
  shrink _ = []

-- | Generate a random expression for testing in GHCi
--
-- Usage:
--   > sample randomExpr
--   > sample (randomExprOfType (TNumber TI32))
--   > sample (randomExprWithDepth 3)
randomExpr :: Gen (Either TypeError (Expr Type))
randomExpr = fmap tc $ arbitrary
  where
    tc :: Expr Type -> Either TypeError (Expr Type)
    tc = infer . fmap (const ())

irandomExpr :: Gen (Either TypeError (Expr Type, [Value]))
irandomExpr = fmap (fmap (\e -> (e, tinterpretToList e)) . tc) $ arbitrary
  where
    tc :: Expr Type -> Either TypeError (Expr Type)
    tc = infer . fmap (const ())

-- | Generate a random expression of a specific type
randomExprOfType :: Type -> Gen (Expr Type)
randomExprOfType = genExprOfType emptyCtx

-- | Generate a random expression with a specific maximum depth
randomExprWithDepth :: Int -> Gen (Expr Type)
randomExprWithDepth depth = do
  targetType <- genType 2
  genExprOfType (emptyCtx { maxDepth = depth }) targetType

-- | Generate a random ERec expression for testing in GHCi
--
-- Usage:
--   > sample randomERec
randomERec :: Gen (Expr Type)
randomERec = do
  recType <- genNonFuncType 2
  genRec emptyCtx recType

irandomERec :: Gen (Either TypeError (Expr Type, [Value]))
irandomERec = fmap (fmap (\e -> (e, tinterpretToList e)) . tc) $ randomERec
  where
    tc :: Expr Type -> Either TypeError (Expr Type)
    tc = infer . fmap (const ())
