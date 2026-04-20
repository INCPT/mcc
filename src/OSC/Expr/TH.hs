{-# OPTIONS -Wno-unused-binds #-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.TH (genSum, genDiff, genBitraversableInstance, genSmartConstructors, genPatternSynonyms) where

import Control.Monad (forM_, forM, foldM)
import Data.Char (toLower)

import qualified Data.Foldable as F

import Language.Haskell.TH

import OSC.Expr.Bitraversable
import OSC.Expr.Functors

-- Documentation ---------------------------------------------------------------
--
-- This module provides Template Haskell functions for generating boilerplate
-- code for working with recursive expression types. It supports:
--
-- 1. Creating sum types that combine multiple expression types
-- 2. Creating difference types (sum minus a subset)
-- 3. Generating Bitraversable instances for transformations between types
--
-- Example Usage:
-- ==============
--
-- Given the following input types:

data Value exp  = Const Int | Arr [exp]
  deriving (Functor, Foldable, Traversable)

data Expr exp
  = NoFields
  | Add exp exp
  | Mul (Maybe (Either String [exp])) exp
  deriving (Functor, Foldable, Traversable)

data FuncRef exp = FuncRef Int
  deriving (Functor, Foldable, Traversable)

data Lambda exp = Lambda String [(String, exp)] exp
  deriving (Functor, Foldable, Traversable)

-- Creating smart constructors:
-- --------------------
--
-- $(genSmartConstructors ''Expr)
--
-- This generates smart constructor functions for each constructor of the type.
-- Each smart constructor:
-- 1. Takes the same arguments as the original constructor
-- 2. Replaces occurrences of the recursive type variable with the concrete type (f Expr)
-- 3. Calls embed before returning
--
-- For example, given:
--   data Expr exp = NoFields | Add exp exp | Mul (Maybe (Either String [exp])) exp
--
-- It generates:

noFields :: Corecursive f => f Expr
noFields = embed NoFields

add :: Corecursive f => f Expr -> f Expr -> f Expr
add a b = embed $ Add a b

mul :: Corecursive f => (Maybe (Either String [f Expr])) -> f Expr -> f Expr
mul a b = embed $ Mul a b

-- The generated functions have a Corecursive constraint and return f Expr, allowing them
-- to work with any wrapper type (Fix, Ann, Dag, etc.) that implements Corecursive.

-- For nested types like:

data A exp = A1 Int String | A2 Float
data B exp = B1 String
data Comp exp = CompA (A exp) | CompB (B exp)

-- $(genSmartConstructors ''Comp) generates:

a1 :: Corecursive f => Int -> String -> f Comp
a1 a b = embed $ CompA $ A1 a b

a2 :: Corecursive f => Float -> f Comp
a2 c = embed $ CompA $ A2 c

b1 :: Corecursive f => String -> f Comp
b1 c = embed $ CompB $ B1 c

-- Creating pattern synonyms:
-- ---------------------------
--
-- $(genPatternSynonyms ''Comp)
--
-- For a type with constructors wrapping other types:
--   data A = A1 a b | A2 c
--   data B = B1 d e
--   data Comp = CompA A | CompB B
--
-- This generates pattern synonyms that match through both layers:

pattern PA1 :: Int -> String -> (Comp exp)
pattern PA1 a b = CompA (A1 a b)

pattern PA2 :: Float -> (Comp exp)
pattern PA2 c = CompA (A2 c)

pattern PB1 :: String -> (Comp exp)
pattern PB1 c = CompB (B1 c)

-- And a COMPLETE pragma:

{-# COMPLETE PA1, PA2, PB1 #-}

-- Creating a Sum Type:
-- --------------------
--
-- $(genSum "S1_" "Sum1" [''Value, ''Expr, ''FuncRef])
--
-- This generates a sum type with single-valued constructors wrapping each type:

data Sum1 exp
  = S1_Value (Value exp)
  | S1_Expr (Expr exp)
  | S1_FuncRef (FuncRef exp)
  deriving (Functor, Foldable, Traversable)

-- Creating a Difference Type:
-- ----------------------------
--
-- $(genDiff "D1_" "Diff1" ''Sum1 ''Value)
--
-- This generates a type containing constructors from Sum1 whose wrapped type
-- is NOT in Value. Constructors must be single-valued (wrapping exactly one type).

data Diff1 exp
  = D1_Expr (Expr exp)
  | D1_FuncRef (FuncRef exp)
  deriving (Functor, Foldable, Traversable)

-- Creating a Bitraversable Instance:
-- -----------------------------------
--
-- $(genBitraversableInstance ''Sum1 ''Value ''Diff1)
--
-- This generates a Bitraversable instance that allows transforming Sum1 expressions
-- into Value expressions. For subset constructors (those wrapping Value), it unwraps
-- and applies trav. For diff constructors, it rewraps in the diff type and calls f:

instance Bitraversable Sum1 Value Diff1 where
  bitraverse trav f = trav go
    where
      go (S1_Value v) = traverse (trav go) v
      go (S1_Expr e) = f (D1_Expr e)
      go (S1_FuncRef e) = f (D1_FuncRef e)

-- Note: Trailing underscores are automatically stripped from constructor names,
-- so you can use empty prefixes ("") when the sum types are in the same module.

data Sum2 exp
  -- from Value
  = S2_Const Int
  | S2_Arr [exp]

  -- from Expr
  | S2_Mul (Maybe (Either String [exp])) exp

  -- from FuncRef
  | S2_FuncRef Int
  deriving (Functor, Foldable, Traversable)

data Diff2 exp
  = D2_NoFields
  | D2_Add exp exp
  | D2_Add2 exp [exp]

data Part2 exp
  = P2_Mul (Maybe (Either String [exp])) exp

-- instance Partition Sum1 Sum2 Diff2 Part2 where
--    partition trav f1 f2 = trav f3
--      where
--         f3 (S1_Const n) = S2_Const <$> pure n
--         f3 (S1_Arr as) = S2_Arr <$> traverse (trav f3) as
--         f3 (S1_Add a b) = f1 (D2_Add a b)
--         f3 (S1_Mul a b) = f2 (P2_Mul a b)
--         f3 _ = undefined

-- Helper functions ------------------------------------------------------------

foldl1M :: Monad m => (a -> a -> m a) -> [a] -> m a
foldl1M _ [] = error "foldl1M: empty list"
foldl1M _ [x] = pure x
foldl1M f (x:xs) = foldM f x xs

validateTypeParams :: Name -> Info -> Q ()
validateTypeParams typeName (TyConI (DataD _ _ tvbs _ _ _)) =
  case length tvbs of
    1 -> pure ()
    n -> fail $ "Type " ++ nameBase typeName ++ " must have exactly 1 type parameter, but has " ++ show n
validateTypeParams typeName _ = 
  fail $ "Expected a data type declaration for " ++ nameBase typeName

getConstructors :: Info -> [(Name, [BangType])]
getConstructors (TyConI (DataD _ _ _ _ cons _)) = 
  [ (name, fields) | NormalC name fields <- cons ]
getConstructors _ = []

validateNoExistentials :: Name -> Info -> Q ()
validateNoExistentials typeName (TyConI (DataD _ _ _ _ cons _)) = do
  forM_ cons $ \con -> case con of
    ForallC _ _ _ -> fail $ "Type " ++ nameBase typeName ++ " has existentially quantified constructor, which is not supported"
    _ -> pure ()
validateNoExistentials _ _ = pure ()


replaceExpType :: Name -> BangType -> BangType
replaceExpType expVar (bang, typ) = (bang, replaceInType expVar typ)

replaceInType :: Name -> Type -> Type
replaceInType expVar typ = case typ of
  VarT _ -> VarT expVar
  AppT f a -> AppT (replaceInType expVar f) (replaceInType expVar a)
  ConT name -> ConT name
  _ -> typ

-- Check if a type contains a type variable in positive position (i.e., is recursive)
-- This handles cases like Maybe f, [f], Either a f, etc.
isRecursiveType :: Type -> Bool
isRecursiveType typ = case typ of
  VarT _ -> True
  AppT _ a -> isRecursiveType a  -- Only check the argument, not the constructor
  _ -> False

-- Count the nesting depth of containers before reaching the recursive type variable
-- e.g., Maybe exp -> 1, Maybe (Maybe exp) -> 2, [Maybe exp] -> 2
containerDepth :: Type -> Int
containerDepth typ = case typ of
  VarT _ -> 0
  AppT _ a -> 1 + containerDepth a
  _ -> 0


-- TODO: specialize once BiPlate is gone
-- Build a constructor application with transformed fields using <$> and <*>
-- Takes a field transformation function as a parameter
genConstructorAppWith :: Name -> [BangType] -> [Name] -> (Type -> Name -> Q Exp) -> Q Exp
genConstructorAppWith conName fields fieldVars transformField = do
  transformedFields <- forM (zip fields fieldVars) $ \((_, typ), var) ->
    transformField typ var
  
  let con = conE conName
  case transformedFields of
    [] -> error "genConstructorAppWith: empty fields"
    [field] -> [| $(con) <$> $(pure field) |]
    (field:rest) -> do
      initial <- [| $(con) <$> $(pure field) |]
      foldM (\acc f -> [| $(pure acc) <*> $(pure f) |]) initial rest

-- Build a constructor application with transformed fields using <$> and <*>
genConstructorApp :: Name -> [BangType] -> [Name] -> Name -> Name -> Name -> Q Exp
genConstructorApp conName fields fieldVars unwrapVar wrapVar fVar =
  genConstructorAppWith conName fields fieldVars $ \typ var ->
    genFieldTransform typ var unwrapVar wrapVar fVar

--------------------------------------------------------------------------------

{-# INLINE foldMapM #-}
foldMapM :: Applicative f => Monoid b => (a -> f b) -> [a] -> f b
foldMapM f = fmap mconcat . traverse f

{-# INLINE foldList #-}
foldList :: Foldable t => [t a] -> [a]
foldList = mconcat . fmap F.toList

--------------------------------------------------------------------------------

genSum :: String -> String -> [Name] -> Q [Dec]
genSum prefix sumName typeNames = do
  let expVar = mkName "exp"
  let sumTypeName = mkName sumName
  
  -- Build constructors: one per input type, wrapping that type
  sumCons <- forM typeNames $ \typeName -> do
    let baseName = nameBase typeName
    let newConName = mkName (prefix ++ baseName)
    let wrappedType = AppT (ConT typeName) (VarT expVar)
    pure $ NormalC newConName [(Bang NoSourceUnpackedness NoSourceStrictness, wrappedType)]

  let sumDataDec = DataD [] sumTypeName [PlainTV expVar BndrReq] Nothing sumCons
        [DerivClause Nothing [ConT ''Functor, ConT ''Foldable, ConT ''Traversable, ConT ''Show]]

  pure [sumDataDec]

genDiff :: String -> String -> Name -> Name -> Q [Dec]
genDiff prefix diffName type1Name type2Name = do
  -- Get constructors of type1
  type1Info <- reify type1Name
  validateTypeParams type1Name type1Info
  validateNoExistentials type1Name type1Info
  let type1Cons = getConstructors type1Info

  -- Get constructors of type2
  type2Info <- reify type2Name
  validateTypeParams type2Name type2Info
  validateNoExistentials type2Name type2Info
  let type2Cons = getConstructors type2Info

  -- Extract wrapped type names from type2 constructors
  type2TypeNames <- forM type2Cons $ \(conName, fields) -> case fields of
    [(_, AppT (ConT typeName) _)] -> pure typeName
    _ -> fail $ "Constructor " ++ nameBase conName ++ " in " ++ nameBase type2Name ++ " must have exactly one field wrapping a type"

  let expVar = mkName "exp"
  let diffTypeName = mkName diffName

  -- Build diff constructors: include type1 constructors whose wrapped type is NOT in type2
  diffCons <- foldMapM (\(conName, fields) -> case fields of
    [(bang, AppT (ConT typeName) _)] ->
      if typeName `elem` type2TypeNames
        then pure []
        else do
          let baseName = nameBase conName
          let newConName = mkName (prefix ++ baseName)
          let wrappedType = AppT (ConT typeName) (VarT expVar)
          pure [NormalC newConName [(bang, wrappedType)]]
    _ -> fail $ "Constructor " ++ nameBase conName ++ " in " ++ nameBase type1Name ++ " must have exactly one field wrapping a type"
    ) type1Cons

  let diffDataDec = DataD [] diffTypeName [PlainTV expVar BndrReq] Nothing diffCons []

  pure [diffDataDec]

--------------------------------------------------------------------------------

genSmartConstructors :: Name -> Q [Dec]
genSmartConstructors typeName = do
  info <- reify typeName
  validateTypeParams typeName info
  validateNoExistentials typeName info
  
  let cons = getConstructors info
  let fVar = mkName "f"
  
  -- Generate smart constructors for each constructor
  -- If a constructor wraps another type, generate smart constructors for the inner type's constructors
  mconcat <$> forM cons (\(conName, fields) -> case fields of
    [(_, AppT (ConT innerTypeName) _)] -> do
      -- This constructor wraps another type, generate smart constructors for inner constructors
      innerInfo <- reify innerTypeName
      let innerCons = getConstructors innerInfo
      mconcat <$> forM innerCons (\(innerConName, innerFields) -> do
        let smartName = mkName (lowerFirst (nameBase innerConName))
        genNestedSmartConstructor typeName conName innerConName innerFields fVar)
    _ -> do
      -- Regular constructor
      let smartName = mkName (lowerFirst (nameBase conName))
      genSmartConstructor typeName smartName conName fields fVar)

-- Helper to lowercase the first character
lowerFirst :: String -> String
lowerFirst [] = []
lowerFirst (c:cs) = toLower c : cs

-- Generate a single smart constructor for a regular constructor
genSmartConstructor :: Name -> Name -> Name -> [BangType] -> Name -> Q [Dec]
genSmartConstructor typeName smartName conName fields fVar = do
  paramVars <- forM [1..length fields] $ \i -> pure $ mkName ("a" ++ show i)
  
  let wrapConstraint = AppT (ConT ''Corecursive) (VarT fVar)
  let returnType = AppT (VarT fVar) (ConT typeName)
  let paramTypes = [ replaceExpWithWrapped fVar typeName typ | (_, typ) <- fields ]
  
  let funType = ForallT [PlainTV fVar SpecifiedSpec] [wrapConstraint] $
        foldr (\paramType acc -> AppT (AppT ArrowT paramType) acc) returnType paramTypes
  
  let conApp = foldl AppE (ConE conName) (fmap VarE paramVars)
  let body = AppE (VarE 'embed) conApp
  let funClause = Clause (fmap VarP paramVars) (NormalB body) []
  
  pure
    [ SigD smartName funType
    , FunD smartName [funClause]
    ]

-- Generate a smart constructor for a nested constructor (outer wraps inner)
genNestedSmartConstructor :: Name -> Name -> Name -> [BangType] -> Name -> Q [Dec]
genNestedSmartConstructor outerTypeName outerConName innerConName innerFields fVar = do
  paramVars <- forM [1..length innerFields] $ \i -> pure $ mkName ("a" ++ show i)
  
  let smartName = mkName (lowerFirst (nameBase innerConName))
  let wrapConstraint = AppT (ConT ''Corecursive) (VarT fVar)
  let returnType = AppT (VarT fVar) (ConT outerTypeName)
  let paramTypes = [ replaceExpWithWrapped fVar outerTypeName typ | (_, typ) <- innerFields ]
  
  let funType = ForallT [PlainTV fVar SpecifiedSpec] [wrapConstraint] $
        foldr (\paramType acc -> AppT (AppT ArrowT paramType) acc) returnType paramTypes
  
  -- Build: embed $ OuterCon $ InnerCon a1 a2 ...
  let innerConApp = foldl AppE (ConE innerConName) (fmap VarE paramVars)
  let outerConApp = AppE (ConE outerConName) innerConApp
  let body = AppE (VarE 'embed) outerConApp
  let funClause = Clause (fmap VarP paramVars) (NormalB body) []
  
  pure
    [ SigD smartName funType
    , FunD smartName [funClause]
    ]

-- Replace occurrences of the type variable with (f TypeName)
replaceExpWithWrapped :: Name -> Name -> Type -> Type
replaceExpWithWrapped fVar typeName typ = case typ of
  VarT _ -> AppT (VarT fVar) (ConT typeName)
  AppT t1 t2 -> AppT (replaceExpWithWrapped fVar typeName t1) (replaceExpWithWrapped fVar typeName t2)
  ConT name -> ConT name
  _ -> typ

--------------------------------------------------------------------------------

genBitraversableInstance :: Name -> Name -> Name -> Q [Dec]
genBitraversableInstance sumTypeName destTypeName diffTypeName = do
  -- Get constructors of sum type
  sumInfo <- reify sumTypeName
  let sumCons = getConstructors sumInfo

  -- Get constructors of dest type
  destInfo <- reify destTypeName
  let destCons = getConstructors destInfo

  -- Get constructors of diff type
  diffInfo <- reify diffTypeName
  let diffCons = getConstructors diffInfo

  -- Extract wrapped type names from dest and diff constructors
  destTypeNames <- forM destCons $ \(conName, fields) -> case fields of
    [(_, AppT (ConT typeName) _)] -> pure typeName
    _ -> fail $ "Constructor " ++ nameBase conName ++ " in " ++ nameBase destTypeName ++ " must wrap exactly one type"

  diffTypeNames <- forM diffCons $ \(conName, fields) -> case fields of
    [(_, AppT (ConT typeName) _)] -> pure typeName
    _ -> fail $ "Constructor " ++ nameBase conName ++ " in " ++ nameBase diffTypeName ++ " must wrap exactly one type"

  let travVar = mkName "trav"
  let fVar = mkName "f"
  let goVar = mkName "go"

  -- Generate clauses for each sum constructor
  goClauses <- forM sumCons $ \(sumConName, fields) -> case fields of
    [(_, AppT (ConT wrappedTypeName) _)] -> do
      let varName = mkName "v"
      let pat = ConP sumConName [] [VarP varName]

      if wrappedTypeName `elem` destTypeNames
        then do
          -- Subset constructor: traverse (trav go) v
          let body = NormalB $ AppE (AppE (VarE 'traverse) (AppE (VarE travVar) (VarE goVar))) (VarE varName)
          pure $ Clause [pat] body []
        else if wrappedTypeName `elem` diffTypeNames
          then do
            -- Diff constructor: find matching diff constructor and call f
            diffConName <- case [ cn | (cn, [(_, AppT (ConT tn) _)]) <- diffCons, tn == wrappedTypeName ] of
              [cn] -> pure cn
              [] -> fail $ "No matching diff constructor for " ++ nameBase sumConName
              _ -> fail $ "Multiple matching diff constructors for " ++ nameBase sumConName
            let body = NormalB $ AppE (VarE fVar) (AppE (ConE diffConName) (VarE varName))
            pure $ Clause [pat] body []
          else fail $ "Constructor " ++ nameBase sumConName ++ " wraps type not in dest or diff"
    _ -> fail $ "Constructor " ++ nameBase sumConName ++ " must wrap exactly one type"

  let goFunc = FunD goVar goClauses
  let bitraverseBody = AppE (VarE travVar) (VarE goVar)
  let bitraverseClause = Clause
        [VarP travVar, VarP fVar]
        (NormalB bitraverseBody)
        [goFunc]

  pure
    [ InstanceD Nothing []
        (AppT (AppT (AppT (ConT ''Bitraversable) (ConT sumTypeName)) (ConT destTypeName)) (ConT diffTypeName))
        [FunD 'bitraverse [bitraverseClause]]
    ]


-- Transform a field based on its type structure
genFieldTransform :: Type -> Name -> Name -> Name -> Name -> Q Exp
genFieldTransform typ var unwrapVar wrapVar fVar
  | not (isRecursiveType typ) = [| pure $(varE var) |]  -- Non-recursive: wrap in pure
  | otherwise = case typ of
      VarT _ -> 
        -- Direct recursive: transformBi unwrap wrap f var
        [| transformBiM $(varE unwrapVar) $(varE wrapVar) $(varE fVar) $(varE var) |]
      AppT _ _ ->
        -- Container: traverse (transformBiM unwrap wrap f) var
        -- Handle nested containers by counting depth
        let depth = containerDepth typ
        in if depth == 1
          then [| traverse (transformBiM $(varE unwrapVar) $(varE wrapVar) $(varE fVar)) $(varE var) |]
          else genNestedTraverse depth var unwrapVar wrapVar fVar
      _ -> varE var

-- Handle nested containers like Maybe (Either String [exp])
genNestedTraverse :: Int -> Name -> Name -> Name -> Name -> Q Exp
genNestedTraverse depth var unwrapVar wrapVar fVar =
  [| (traverse $(buildTraverse (depth - 1))) $(varE var) |]
  where
    buildTraverse 0 = [| transformBiM $(varE unwrapVar) $(varE wrapVar) $(varE fVar) |]
    buildTraverse n = [| traverse $(buildTraverse (n - 1)) |]

-- Transform a field for bitraverse subset constructors (using trav go)
genBitraverseSubsetFieldTransform :: Type -> Name -> Name -> Name -> Q Exp
genBitraverseSubsetFieldTransform typ var travVar goVar
  | not (isRecursiveType typ) = [| pure $(varE var) |]  -- Non-recursive: wrap in pure
  | otherwise = case typ of
      VarT _ -> 
        -- Direct recursive: trav go var
        [| $(varE travVar) $(varE goVar) $(varE var) |]
      AppT _ _ ->
        -- Container: traverse (trav go) var (or nested traverse for deeper nesting)
        let depth = containerDepth typ
        in if depth == 1
          then [| traverse ($(varE travVar) $(varE goVar)) $(varE var) |]
          else genBitraverseSubsetNestedTraverse depth var travVar goVar
      _ -> varE var

-- Handle nested containers for bitraverse subset constructors
genBitraverseSubsetNestedTraverse :: Int -> Name -> Name -> Name -> Q Exp
genBitraverseSubsetNestedTraverse depth var travVar goVar =
  [| (traverse $(buildTraverse (depth - 1))) $(varE var) |]
  where
    buildTraverse 0 = [| $(varE travVar) $(varE goVar) |]
    buildTraverse n = [| traverse $(buildTraverse (n - 1)) |]

--------------------------------------------------------------------------------

genPatternSynonyms :: Name -> Q [Dec]
genPatternSynonyms typeName = do
  info <- reify typeName
  validateTypeParams typeName info
  validateNoExistentials typeName info
  
  -- Get type variables from the outer type
  typeVars <- case info of
    TyConI (DataD _ _ tvbs _ _ _) -> pure [ name | PlainTV name _ <- tvbs ]
    _ -> fail $ "Expected a data type declaration for " ++ nameBase typeName
  
  let cons = getConstructors info
  
  -- Generate pattern synonyms for each constructor
  (patternDecs, patternNames) <- fmap mconcat . forM cons $ \(conName, fields) -> case fields of
    [(_, AppT (ConT innerTypeName) _)] -> do
      -- This constructor wraps another type, generate patterns for inner constructors
      innerInfo <- reify innerTypeName
      let innerCons = getConstructors innerInfo
      fmap mconcat . forM innerCons $ \(innerConName, innerFields) -> do
        let patternName = mkName ("P" ++ nameBase innerConName)
        decs <- genPatternSynonym typeName typeVars patternName conName innerConName innerFields
        pure (decs, [patternName])
    _ -> do
      -- Regular constructor - generate a simple pattern
      let patternName = mkName ("P" ++ nameBase conName)
      decs <- genSimplePatternSynonym typeName typeVars patternName conName fields
      pure (decs, [patternName])
  
  -- Generate COMPLETE pragma
  let completePragma = PragmaD $ CompleteP patternNames Nothing
  
  pure (patternDecs ++ [completePragma])

-- Generate a pattern synonym for a nested constructor
genPatternSynonym :: Name -> [Name] -> Name -> Name -> Name -> [BangType] -> Q [Dec]
genPatternSynonym outerTypeName typeVars patternName outerConName innerConName innerFields = do
  paramVars <- forM [1..length innerFields] $ \i -> pure $ mkName ("a" ++ show i)
  
  -- Build the pattern: OuterCon (InnerCon a1 a2 ...)
  let innerPat = ConP innerConName [] (fmap VarP paramVars)
  let outerPat = ConP outerConName [] [innerPat]
  
  -- Build the type signature
  -- Replace any type variables in the inner fields with the outer type's type variables
  let paramTypes = [ replaceTypeVars typeVars (stripBang typ) | (_, typ) <- innerFields ]
  -- Apply type variables to the result type: Expr exp
  let resultType = foldl AppT (ConT outerTypeName) (fmap VarT typeVars)
  let patType = foldr (\paramType acc -> AppT (AppT ArrowT paramType) acc) resultType paramTypes
  
  -- Pattern synonym declaration
  let patSynDec = PatSynD patternName (PrefixPatSyn paramVars) ImplBidir outerPat
  let patSigDec = PatSynSigD patternName patType
  
  pure [patSigDec, patSynDec]

-- Generate a simple pattern synonym for a non-nested constructor
genSimplePatternSynonym :: Name -> [Name] -> Name -> Name -> [BangType] -> Q [Dec]
genSimplePatternSynonym typeName typeVars patternName conName fields = do
  paramVars <- forM [1..length fields] $ \i -> pure $ mkName ("a" ++ show i)
  
  let pat = ConP conName [] (fmap VarP paramVars)
  -- Replace any type variables in the fields with the outer type's type variables
  let paramTypes = [ replaceTypeVars typeVars (stripBang typ) | (_, typ) <- fields ]
  -- Apply type variables to the result type: Expr exp
  let resultType = foldl AppT (ConT typeName) (fmap VarT typeVars)
  let patType = foldr (\paramType acc -> AppT (AppT ArrowT paramType) acc) resultType paramTypes
  
  let patSynDec = PatSynD patternName (PrefixPatSyn paramVars) ImplBidir pat
  let patSigDec = PatSynSigD patternName patType
  
  pure [patSigDec, patSynDec]

-- Strip bang annotations from a type
stripBang :: Type -> Type
stripBang typ = typ

-- Replace any type variables in a type with the provided type variables
-- This ensures we use consistent type variable names (e.g., 'exp' instead of 'exp_i26cu')
-- We recursively traverse the entire type structure to replace all occurrences
replaceTypeVars :: [Name] -> Type -> Type
replaceTypeVars typeVars = go
  where
    go typ = case typ of
      VarT _ -> case typeVars of
        [v] -> VarT v  -- Single type variable case
        _ -> typ       -- Multiple type variables - keep as is for now
      AppT t1 t2 -> AppT (go t1) (go t2)
      ListT -> ListT
      TupleT n -> TupleT n
      ArrowT -> ArrowT
      ConT name -> ConT name
      _ -> typ

