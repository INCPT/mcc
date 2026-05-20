{-# OPTIONS -Wno-orphans #-}

module OSC.Expr.Gen where

import qualified OSC.Expr.Comp as C
import qualified OSC.Expr.Base as B
import OSC.Expr.Base
import OSC.Expr.Functors

import Test.QuickCheck
import qualified Test.QuickCheck as T
import Control.Monad (replicateM)
import qualified Data.Map as M
import Data.Map (Map)

import qualified OSC.Expr.Interpret as I
import qualified OSC.Codegen.Interpret as C

import OSC.Codegen
import OSC.Transforms.Typecheck
import OSC.Transforms.AnnBind
import OSC.Transforms.FoldSel
import OSC.Transforms.Defunc

-- | Generate non-zero numeric constants (heavily biased against 0)
genNonZeroI32 :: Corecursive f => Gen (f Expr)
genNonZeroI32 = B.const . C.I32 <$> frequency [(9, arbitrary `suchThat` (/= 0)), (1, pure 0)]

genNonZeroF32 :: Corecursive f => Gen (f Expr)
genNonZeroF32 = B.const . C.F32 <$> frequency [(9, arbitrary `suchThat` (/= 0)), (1, pure 0)]

genNonZeroI64 :: Corecursive f => Gen (f Expr)
genNonZeroI64 = B.const . C.I64 <$> frequency [(9, arbitrary `suchThat` (/= 0)), (1, pure 0)]

genNonZeroF64 :: Corecursive f => Gen (f Expr)
genNonZeroF64 = B.const . C.F64 <$> frequency [(9, arbitrary `suchThat` (/= 0)), (1, pure 0)]

-- | Generate a random identifier
genIdent :: Gen C.Ident
genIdent = do
  prefix <- elements ["x", "y", "z", "a", "b", "c", "f", "g"]
  suffix <- choose (0, 999 :: Int)
  pure $ C.Ident (prefix <> show suffix)

-- | Generate n unique identifiers
genUniqueIdents :: Int -> Gen [C.Ident]
genUniqueIdents n = go n []
  where
    go 0 acc = pure acc
    go remaining acc = do
      ident <- genIdent
      if ident `elem` acc
        then go remaining acc  -- Try again if duplicate
        else go (remaining - 1) (ident : acc)

-- | Generate a unique identifier not in the given list
genUniqueIdentNotIn :: [C.Ident] -> Gen C.Ident
genUniqueIdentNotIn existing = do
  ident <- genIdent
  if ident `elem` existing
    then genUniqueIdentNotIn existing  -- Try again if duplicate
    else pure ident

-- | Generate a random type
genType :: Int -> Gen C.Type
genType depth
  | depth <= 0 = genSimpleType
  | otherwise = frequency
      [ (3, genSimpleType)
      , (1, genArrayType)
      , (1, genFuncType)
      ]
  where
    genSimpleType = C.TNumber <$> elements [C.TI32, C.TF32, C.TI64, C.TF64]
    
    genArrayType = do
      elemType <- genType (depth - 1)
      len <- choose (1, 5)
      pure $ C.TArr elemType len
    
    genFuncType = do
      numParams <- choose (0, 3)
      params <- replicateM numParams (genType (depth - 1))
      retType <- genType (depth - 1)
      pure $ C.TLam params retType

genSimpleType :: Gen C.Type
genSimpleType = C.TNumber <$> elements [C.TI32, C.TF32, C.TI64, C.TF64]

-- | Generate a type that doesn't contain functions (for ERec)
genNonFuncType :: Int -> Gen C.Type
genNonFuncType depth
  | depth <= 0 = genSimpleType
  | otherwise = frequency
      [ (3, genSimpleType)
      , (1, genArrayType)
      ]
  where
    genArrayType = do
      elemType <- genNonFuncType (depth - 1)
      len <- choose (1, 5)
      pure $ C.TArr elemType len

-- | Context for generating expressions with available variables
data GenCtx = GenCtx
  { availableVars :: Map C.Ident C.Type
  , maxDepth :: Int
  }

emptyCtx :: GenCtx
emptyCtx = GenCtx M.empty 5

withVar :: C.Ident -> C.Type -> GenCtx -> GenCtx
withVar ident t ctx = ctx { availableVars = M.insert ident t (availableVars ctx) }

withVars :: [(C.Ident, C.Type)] -> GenCtx -> GenCtx
withVars vars ctx = ctx { availableVars = M.fromList vars <> availableVars ctx }

-- | Generate an expression of a specific type
genExprOfType :: forall f. Corecursive f => GenCtx -> C.Type -> Gen (f Expr)
genExprOfType ctx targetType = sized $ \size ->
  if size <= 0 || maxDepth ctx <= 0
    then genLeaf ctx targetType
    else frequency
      [ (2, genLeaf ctx targetType)
      , (5, genComposite ctx targetType)
      ]

-- | Generate leaf expressions (constants and variables)
genLeaf :: Corecursive f => GenCtx -> C.Type -> Gen (f Expr)
genLeaf ctx (C.TNumber C.TI32) = case genVarOfType ctx (C.TNumber C.TI32) of
  Just varGen -> frequency [(3, genNonZeroI32), (1, varGen)]
  Nothing -> genNonZeroI32
genLeaf ctx (C.TNumber C.TF32) = case genVarOfType ctx (C.TNumber C.TF32) of
  Just varGen -> frequency [(3, genNonZeroF32), (1, varGen)]
  Nothing -> genNonZeroF32
genLeaf ctx (C.TNumber C.TI64) = case genVarOfType ctx (C.TNumber C.TI64) of
  Just varGen -> frequency [(3, genNonZeroI64), (1, varGen)]
  Nothing -> genNonZeroI64
genLeaf ctx (C.TNumber C.TF64) = case genVarOfType ctx (C.TNumber C.TF64) of
  Just varGen -> frequency [(3, genNonZeroF64), (1, varGen)]
  Nothing -> genNonZeroF64
genLeaf ctx t@(C.TArr elemType len) = case genVarOfType ctx t of
  Just varGen -> frequency [(3, genArray ctx elemType len), (1, varGen)]
  Nothing -> genArray ctx elemType len
genLeaf ctx t@(C.TLam _ _) = case genVarOfType ctx t of
  Just varGen -> varGen
  Nothing -> genAbs ctx (C.paramTypes "genLeaf" t) (C.returnType t)

-- | Generate a variable reference of a specific type (returns Nothing if no vars available)
genVarOfType :: Corecursive f => GenCtx -> C.Type -> Maybe (Gen (f Expr))
genVarOfType ctx targetType =
  if null varsOfType
    then Nothing
    else Just $ do
      (ident, _) <- elements varsOfType
      pure $ iVar ident
  where
    varsOfType = M.toList $ M.filter (== targetType) (availableVars ctx)

-- | Generate composite expressions
genComposite :: Corecursive f => GenCtx -> C.Type -> Gen (f Expr)
genComposite ctx t@(C.TNumber _) = oneof
  [ genBinOp ctx t
  , genSelect ctx t
  , genApp ctx t
  , genRec ctx t
  ]
genComposite ctx t@(C.TArr elemType len) = oneof
  [ genArray ctx elemType len
  , genSelect ctx t
  , genApp ctx t
  , genRec ctx t
  ]
genComposite ctx t@(C.TLam params retType) = oneof
  [ genAbs ctx params retType
  , genApp ctx t
  ]

-- | Generate a binary operation
genBinOp :: Corecursive f => GenCtx -> C.Type -> Gen (f Expr)
genBinOp ctx t@(C.TNumber _) = do
  op <- elements [C.Add, C.Sub, C.Mul, C.And, C.Or, C.Xor, C.Min, C.Max]

  let ctx' = ctx { maxDepth = maxDepth ctx - 1 }

  a <- scale (`div` 2) $ genExprOfType ctx' t
  b <- scale (`div` 2) $ genExprOfType ctx' t

  pure $ B.op op a b
genBinOp _ t = error $ "genBinOp: not a number type: " ++ show t

-- | Generate an array
genArray :: Corecursive f => GenCtx -> C.Type -> Int -> Gen (f Expr)
genArray ctx elemType len = do
  let ctx' = ctx { maxDepth = maxDepth ctx - 1 }
  elems <- replicateM len (scale (`div` len) $ genExprOfType ctx' elemType)
  pure $ arr elems

-- | Generate an array selection with in-bounds index
genSelect :: Corecursive f => GenCtx -> C.Type -> Gen (f Expr)
genSelect ctx targetType = do
  -- Generate an array that contains elements of targetType
  arrLen <- choose (1, 5)
  let arrType = C.TArr targetType arrLen
  let ctx' = ctx { maxDepth = maxDepth ctx - 1 }
  
  arr <- scale (`div` 2) $ genExprOfType ctx' arrType
  
  -- Generate an in-bounds index (0 to arrLen-1)
  idxVal <- choose (0, arrLen - 1)
  let idx = B.const (C.I32 idxVal)
  
  pure $ select arr idx

-- | Generate a function application
genApp :: Corecursive f => GenCtx -> C.Type -> Gen (f Expr)
genApp ctx retType = do
  -- Generate function type
  numParams <- choose (0, 3)
  paramTypes <- replicateM numParams (genType 2)
  let funcType = C.TLam paramTypes retType
  let ctx' = ctx { maxDepth = maxDepth ctx - 1 }
  
  -- Generate function expression
  func <- scale (`div` 2) $ genExprOfType ctx' funcType
  
  -- Generate arguments of correct types
  args <- mapM (scale (`div` 2) . genExprOfType ctx') paramTypes
  
  pure $ app func args

-- | Generate an abstraction with bindings
genAbs :: Corecursive f => GenCtx -> [C.Type] -> C.Type -> Gen (f Expr)
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
  
  pure $ lam (C.TLam paramTypes retType) paramNames bindings body

-- | Generate a list of bindings where each can reference previous ones
-- The bindings are shuffled so earlier bindings may reference later ones
genBindings :: Corecursive f => GenCtx -> Int -> Gen ([(C.Ident, f Expr)], GenCtx)
genBindings ctx 0 = pure ([], ctx)
genBindings ctx n = do
  -- Generate all bindings in dependency order
  (bindings, finalCtx) <- genBindingsInOrder ctx n
  
  -- Shuffle the bindings
  shuffledBindings <- shuffle bindings
  
  pure (shuffledBindings, finalCtx)

-- | Generate bindings in dependency order (helper for genBindings)
genBindingsInOrder :: Corecursive f => GenCtx -> Int -> Gen ([(C.Ident, f Expr)], GenCtx)
genBindingsInOrder ctx 0 = pure ([], ctx)
genBindingsInOrder ctx n = do
  -- Generate a unique binding name (not already in context)
  bindingName <- genUniqueIdentNotIn (M.keys $ availableVars ctx)
  bindingType <- genType 2
  let ctx' = ctx { maxDepth = maxDepth ctx - 1 }
  bindingExpr <- scale (`div` 2) $ genExprOfType ctx' bindingType
  
  -- Add this binding to context for subsequent bindings
  let newCtx = withVar bindingName bindingType ctx
  
  -- Generate remaining bindings
  (restBindings, finalCtx) <- genBindingsInOrder newCtx (n - 1)
  
  pure ((bindingName, bindingExpr) : restBindings, finalCtx)

-- | Generate a recursive expression (ERec)
-- The type cannot contain functions, and the recursive parameter represents
-- the previous value in the recursive computation
genRec :: Corecursive f => GenCtx -> C.Type -> Gen (f Expr)
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
  
  pure $ B.rec recType delay paramName bindings body
  where

    -- Generate a body expression that uses the recursive parameter
    genBodyUsingParam :: Corecursive f => GenCtx -> C.Type -> C.Ident -> Gen (f Expr)
    genBodyUsingParam ctx t@(C.TNumber _) paramName = oneof
      [ -- Binary operation with the recursive parameter
        do
          op <- elements [C.Add, C.Sub]
          other <- scale (`div` 2) $ genExprOfType ctx t
          -- Randomly put param on left or right
          elements
            [ B.op op (iVar paramName) other
            , B.op op other (iVar paramName)
            ]
      , -- Use param in a more complex expression
        do
          op1 <- elements [C.Add, C.Sub]
          op2 <- elements [C.Add, C.Sub]
          a <- scale (`div` 3) $ genExprOfType ctx t
          b <- scale (`div` 3) $ genExprOfType ctx t
          B.op op1 <$> (B.op op2 (iVar paramName) <$> pure a) <*> pure b
      ]
    genBodyUsingParam ctx (C.TArr elemType len) paramName = oneof
      [ -- Select from the recursive parameter array
        do
          idxVal <- choose (0, len - 1)
          idx <- elements [B.const (C.I32 idxVal), B.const (C.I64 idxVal)]
          pure $ select (iVar paramName) idx
      , -- Build array using recursive parameter elements
        do
          indices <- replicateM len $ choose (0, len - 1)
          elems <- mapM mkSelect indices
          pure $ arr elems
      , -- Combine recursive param with other values in array
        do
          idxVal <- choose (0, len - 1)
          idx <- elements [B.const (C.I32 idxVal), B.const (C.I64 idxVal)]
          otherElems <- replicateM (len - 1) (scale (`div` len) $ genExprOfType ctx elemType)
          pos <- choose (0, len - 1)
          let (before, after) = splitAt pos otherElems
          let paramElem = select (iVar paramName) idx
          pure $ arr (before <> [paramElem] <> after)
      ]
      where
        mkSelect i = do
          idx <- elements [B.const (C.I32 i), B.const (C.I64 i)]
          pure $ select (iVar paramName) idx
    genBodyUsingParam _ _ paramName = 
      -- Fallback: just return the parameter itself
      pure $ iVar paramName

-- | Arbitrary instance for Fix Expr
instance Arbitrary (Fix Expr) where
  arbitrary = do
    returnType <- genSimpleType
    genExprOfType emptyCtx returnType
  
  shrink (Fix (PConst (C.I32 n))) = [Fix (PConst (C.I32 n')) | n' <- shrink n]
  shrink (Fix (PConst (C.I64 n))) = [Fix (PConst (C.I64 n')) | n' <- shrink n]
  shrink (Fix (PConst (C.F32 n))) = [Fix (PConst (C.F32 n')) | n' <- shrink n]
  shrink (Fix (PConst (C.F64 n))) = [Fix (PConst (C.F64 n')) | n' <- shrink n]
  shrink (Fix (POp _ a b)) = [a, b]
  shrink (Fix (PArr es)) = es
  shrink (Fix (PSelect arr _)) = [arr]
  shrink (Fix (PApp f args)) = f : args
  shrink (Fix (PLam _ _ bindings body)) = body : [e | (_,  e) <- bindings]
  shrink (Fix (PRec _ _ _ bindings body)) = body : [e | (_,  e) <- bindings]
  shrink _ = []

-- | Generate a random expression for testing in GHCi
--
-- Usage:
--   > sample randomExpr
--   > sample (randomExprOfType (C.TNumber C.TI32))
--   > sample (randomExprWithDepth 3)
randomExpr :: Gen (Fix Expr)
randomExpr = arbitrary

-- | Generate a random expression of a specific type
randomExprOfType :: C.Type -> Gen (Fix Expr)
randomExprOfType = genExprOfType emptyCtx

-- | Generate a random expression with a specific maximum depth
randomExprWithDepth :: Int -> Gen (Fix Expr)
randomExprWithDepth depth = do
  targetType <- genType 2
  genExprOfType (emptyCtx { maxDepth = depth }) targetType

randomERec :: Gen (Fix Expr)
randomERec = do
  recType <- genNonFuncType 2
  genRec emptyCtx recType

sampleExpr :: IO [Fix Expr]
sampleExpr = T.sample' randomExpr

sampleOneExpr :: IO (Fix Expr)
sampleOneExpr = last <$> T.sample' randomExpr

--------------------------------------------------------------------------------

interpretExpr :: Fix Expr -> [I.Value]
interpretExpr expr = I.interpretToList 20 expr'
   where
      expr' = dbgInfer $ hoist expr

interpretIR :: Fix Expr -> [C.Value]
interpretIR expr = C.interpretToList 20 program
   where
      (expr', dfm) = defunc $ annCapturedBindings $ foldSelections $ dbgInfer $ hoist expr
      program = codegen dfm expr'

cmpValue :: C.Value -> I.Value -> Bool
cmpValue (C.VNumber n) (I.VNumber m) = n == m
cmpValue (C.VArr ns) (I.VArr ms) = and [ cmpValue n m | (n, m) <- zip ns ms ]
cmpValue _ _ = False

test :: Gen Bool
test = do
  expr <- randomExprOfType C.ti32
  let ns = interpretIR expr
  let ms = interpretExpr expr
  pure $ and [ cmpValue n m | (n, m) <- zip ns ms ]