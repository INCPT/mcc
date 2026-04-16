{-# OPTIONS -Wno-unused-binds #-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.TH (Plate (..), BiPlate (..), Empty, genSum, genDiff, genPlateInstance, genBiPlateInstance, genSmartConstructors, universe, transformM, transform) where

import Control.Monad (forM_, forM, foldM, unless, when)
import Data.Char (toLower)

import qualified Data.Foldable as F

import Language.Haskell.TH

import OSC.Expr.Functors (Wrap (wrap), WFunctor (..))
import OSC.Expr.Plate

-- Documentation ---------------------------------------------------------------
--
-- This module provides Template Haskell functions for generating boilerplate
-- code for working with recursive expression types. It supports:
--
-- 1. Creating sum types that combine multiple expression types
-- 2. Generating Plate instances for generic traversal
-- 3. Creating difference types (sum minus a subset)
-- 4. Generating BiPlate instances for transformations between types
--
-- Example Usage:
-- ==============
--
-- Given the following input types:

data Value exp  = Const Int | Arr [exp]

data Expr exp
  = NoFields
  | Add exp exp
  | Mul (Maybe (Either String [exp])) exp

data FuncRef exp = FuncRef Int

data Lambda exp = Lambda String [(String, exp)] exp

-- Creating smart constructors:
-- --------------------
--
-- $(genSmartConstructors ''Expr)
--
-- This generates smart constructor functions for each constructor of the type.
-- Each smart constructor:
-- 1. Takes the same arguments as the original constructor
-- 2. Replaces occurrences of the recursive type variable with the concrete type (f Expr)
-- 3. Calls wrap before returning
--
-- For example, given:
--   data Expr exp = NoFields | Add exp exp | Mul (Maybe (Either String [exp])) exp
--
-- It generates:

noFields :: Wrap f => f Expr
noFields = wrap NoFields

add :: Wrap f => f Expr -> f Expr -> f Expr
add a b = wrap $ Add a b

mul :: Wrap f => (Maybe (Either String [f Expr])) -> f Expr -> f Expr
mul a b = wrap $ Mul a b

-- The generated functions have a Wrap constraint and return f Expr, allowing them
-- to work with any wrapper type (Fix, Ann, Dag, etc.) that implements Wrap.

-- Creating a Sum Type:
-- --------------------
--
-- $(genSum "S1_" "Sum1" [''Value, ''Expr, ''FuncRef])
--
-- This generates a sum type that combines all constructors from Value, Expr,
-- and FuncRef, prefixing each constructor name with "S1_":

data Sum1 exp
  -- from Value
  = S1_Const Int
  | S1_Arr [exp]

  -- from Expr
  | S1_NoFields
  | S1_Add exp exp
  | S1_Add2 exp [exp]
  | S1_Mul (Maybe (Either String [exp])) exp

  -- from FuncRef
  | S1_FuncRef Int
  deriving (Functor, Foldable, Traversable)

-- Generating a Plate Instance:
-- -----------------------------
--
-- $(genPlateInstance ''Sum1)
--
-- This generates a Plate instance that enables generic traversal over the
-- recursive structure. The descend function unwraps each expression, attempts
-- to extract a value, and recursively descends into subexpressions:

instance Plate Sum1 where
  descendM unwrap expr = do
    inner <- unwrap expr
    case inner of
      S1_Const _ -> pure []
      S1_NoFields -> pure []
      S1_Arr exprs -> pure $ mconcat [ F.toList exprs ]
      S1_Add exp1 exp2 -> pure $ mconcat [ [ exp1 ], [ exp2 ] ]
      S1_Mul exp1 exp2 -> pure $ mconcat [ foldList $ F.toList $ foldList $ F.toList exp1, [ exp2 ] ]
      S1_FuncRef _ -> pure []

-- Creating a Difference Type:
-- ----------------------------
--
-- $(genDiff "D1_" "Diff1" "S1_" ''Sum1 "" ''Value)
--
-- This generates a type containing all constructors from Sum1 that are NOT
-- in Value. The result is Sum1 minus Value, with constructors prefixed by "D1_":

data Diff1 exp
  = D1_NoFields
  | D1_Add exp exp
  | D1_Add2 exp [exp]
  | D1_Mul (Maybe (Either String [exp])) exp
  | D1_FuncRef Int
  deriving (Functor, Foldable, Traversable)

-- Generating a BiPlate Instance:
-- -------------------------------
--
-- $(genBiPlateInstance "S1_" ''Sum1 "" ''Value "D1_" ''Diff1)
--
-- This generates a BiPlate instance that transforms between Sum1 and Value,
-- using Diff1 for constructors not in Value. Constructors from Value are
-- wrapped, while others are passed to the transformation function:

instance BiPlate Sum1 Value Diff1 where
  transformBiM unwrap wrap f expr = do
    inner <- unwrap expr
    case inner of
      -- Constructors from Value: wrap the result
      S1_Const n -> wrap =<< (Const <$> pure n)
      S1_Arr as  -> wrap =<< (Arr <$> traverse (transformBiM unwrap wrap f) as)

      -- Constructors from Diff1: apply transformation function
      S1_NoFields ->  f =<< pure D1_NoFields
      S1_Add a b -> f =<< (D1_Add <$> (transformBiM unwrap wrap f) a <*> transformBiM unwrap wrap f b)
      S1_Mul a b -> f =<< (D1_Mul <$> (traverse (traverse (traverse (transformBiM unwrap wrap f)))) a <*> transformBiM unwrap wrap f b)

      -- Constructors from FuncRef
      S1_FuncRef a ->  f =<< pure (D1_FuncRef a)
      _ -> undefined

instance RecPlate Sum1 where
  transformRec wmap (S1_Const n) = pure $ S1_Const n
  transformRec wmap (S1_Arr as) = S1_Arr <$> traverse wmap as
  transformRec wmap (S1_Add a b) = S1_Add <$> wmap a <*> wmap b
  transformRec _ _ = undefined

instance TraversableBi Sum1 Value Diff1 where
  traverseBi g f (S1_Const n) = Const <$> pure n
  traverseBi g f (S1_Arr as) = Arr <$> traverse g as

  traverseBi g f (S1_Add a b) = f =<< (D1_Add <$> g a <*> g b)
  traverseBi g f (S1_Add2 a b) = f =<< (D1_Add2 <$> g a <*> (traverse g b))

  traverseBi g f _ = undefined

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

-- Compare constructors by their fields only, ignoring names
-- Normalize type variables before comparing so we compare structure
consEqualByFields :: (Name, [BangType]) -> (Name, [BangType]) -> Bool
consEqualByFields (_, fields1) (_, fields2) = 
  normalizeFields fields1 == normalizeFields fields2
  where
    normalizeFields = fmap normalizeBangType
    normalizeBangType (bang, typ) = (bang, normalizeType typ)
    normalizeType (VarT _) = VarT (mkName "a")
    normalizeType (AppT f a) = AppT (normalizeType f) (normalizeType a)
    normalizeType t = t

-- Strip a prefix from a string if present
stripPrefix :: String -> String -> Maybe String
stripPrefix prefix str
  | prefix == take (length prefix) str = Just (drop (length prefix) str)
  | otherwise = Nothing

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

-- Match sum constructors to subset/dest constructors by name
-- For each sum constructor, strips the sum prefix and looks up the base name
-- in the subset map. Calls onSubset if found, onDiff if not found.
matchSumConstructors
  :: String                                    -- Sum prefix
  -> [(Name, [BangType])]                      -- Sum constructors
  -> [(String, (Name, [BangType]))]            -- Subset map (baseName -> (conName, fields))
  -> ((Name, [BangType]) -> (Name, [BangType]) -> String -> Q a)  -- onSubset: sumCon -> subsetCon -> baseName -> result
  -> ((Name, [BangType]) -> String -> Q a)     -- onDiff: sumCon -> baseName -> result
  -> Q [a]
matchSumConstructors sumPrefix sumCons subsetMap onSubset onDiff =
  forM sumCons $ \sumCon@(sumConName, _) -> do
    let sumName = nameBase sumConName
    
    case stripPrefix sumPrefix sumName of
      Nothing -> fail $ "Sum constructor " ++ sumName ++ " doesn't have expected prefix " ++ sumPrefix
      Just baseName -> do
        case lookup baseName subsetMap of
          Just (subsetConName, subsetFields) -> do
            unless (consEqualByFields sumCon (subsetConName, subsetFields)) $
              fail $ "Constructor " ++ sumName ++ " has different fields than subset constructor " ++ nameBase subsetConName
            onSubset sumCon (subsetConName, subsetFields) baseName
          Nothing -> onDiff sumCon baseName

-- Build a constructor application with transformed fields using <$> and <*>
genConstructorApp :: Name -> [BangType] -> [Name] -> Name -> Name -> Name -> Q Exp
genConstructorApp conName fields fieldVars unwrapVar wrapVar fVar = do
  transformedFields <- forM (zip fields fieldVars) $ \((_, typ), var) ->
    genFieldTransform typ var unwrapVar wrapVar fVar
  
  let con = conE conName
  case transformedFields of
    [] -> error "genConstructorApp: empty fields"
    [field] -> [| $(con) <$> $(pure field) |]
    (field:rest) -> do
      initial <- [| $(con) <$> $(pure field) |]
      foldM (\acc f -> [| $(pure acc) <*> $(pure f) |]) initial rest

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
  -- Get info about all the types
  typeInfos <- forM typeNames $ \typeName -> do
    info <- reify typeName
    validateTypeParams typeName info
    validateNoExistentials typeName info
    pure (typeName, info)

  -- Collect all constructors from all types
  let allCons = mconcat [ getConstructors info | (_, info) <- typeInfos ]

  -- Create the sum type
  let expVar = mkName "exp"
  let sumTypeName = mkName sumName
  
  -- Build constructors for the sum type
  sumCons <- forM allCons $ \(conName, fields) -> do
    let newConName = mkName (prefix ++ nameBase conName)
    let newFields = fmap (replaceExpType expVar) fields
    pure $ NormalC newConName newFields

  -- Create the data declaration
  let sumDataDec = DataD [] sumTypeName [PlainTV expVar BndrReq] Nothing sumCons
        [DerivClause Nothing [ConT ''Functor, ConT ''Foldable, ConT ''Traversable, ConT ''Show]]

  pure [sumDataDec]

genDiff :: String -> String -> String -> Name -> String -> Name -> Q [Dec]
genDiff prefix diffName sumPrefix sumTypeName subsetPrefix subsetTypeName = do
  -- Get info about the sum type
  sumInfo <- reify sumTypeName
  validateTypeParams sumTypeName sumInfo
  validateNoExistentials sumTypeName sumInfo
  let sumCons = getConstructors sumInfo

  -- Get info about the subset type
  subsetInfo <- reify subsetTypeName
  validateTypeParams subsetTypeName subsetInfo
  validateNoExistentials subsetTypeName subsetInfo
  let subsetCons = getConstructors subsetInfo

  -- Build a map from base names to subset constructors
  let subsetMap = [ (baseName, (conName, fields))
                  | (conName, fields) <- subsetCons
                  , Just baseName <- [stripPrefix subsetPrefix (nameBase conName)]
                  ]

  -- Create the diff type
  let expVar = mkName "exp"
  let diffTypeName = mkName diffName
  
  -- Build constructors for the diff type
  -- Only include sum constructors that don't match any subset constructor
  diffConsDecls <- matchSumConstructors sumPrefix sumCons subsetMap
    (\_ _ _ -> pure Nothing)  -- Skip subset constructors
    (\(_, fields) baseName -> do
      let newConName = mkName (prefix ++ baseName)
      let newFields = fmap (replaceExpType expVar) fields
      pure $ Just $ NormalC newConName newFields
    )

  let diffConsDecls' = [ c | Just c <- diffConsDecls ]

  -- Create the data declaration
  let diffDataDec = DataD [] diffTypeName [PlainTV expVar BndrReq] Nothing diffConsDecls' []

  pure [diffDataDec]

--------------------------------------------------------------------------------

genPlateInstance :: Name -> Q [Dec]
genPlateInstance typeName = do
  info <- reify typeName
  let cons = getConstructors info
  
  let unwrapVar = mkName "unwrap"
  let exprVar = mkName "expr"
  let innerVar = mkName "inner"

  -- Build pattern matches for each constructor
  matches <- forM cons $ \(conName, fields) -> do
    genDescendMatch conName fields

  let descendBody = DoE Nothing
        [ BindS (VarP innerVar) (AppE (VarE unwrapVar) (VarE exprVar))
        , NoBindS (CaseE (VarE innerVar) matches)
        ]

  let descendClause = Clause 
        [VarP unwrapVar, VarP exprVar]
        (NormalB descendBody)
        []

  pure
    [ InstanceD Nothing [] 
        (AppT (ConT ''Plate) (ConT typeName))
        [FunD 'descendM [descendClause]]
    ]

genDescendMatch :: Name -> [BangType] -> Q Match
genDescendMatch conName fields = do
  fieldVars <- forM [1..length fields] $ \i -> pure $ mkName ("_exp" ++ show i)
  
  let pat = ConP conName [] (fmap VarP fieldVars)
  
  -- Filter to only recursive fields (those containing the type variable)
  let recursiveFields = [ (f, v) | (f@(_, typ), v) <- zip fields fieldVars, isRecursiveType typ ]
  
  body <- if null recursiveFields
    then [| pure [] |]
    else genDescendBody recursiveFields

  pure $ Match pat (NormalB body) []

genDescendBody :: [((Bang, Type), Name)] -> Q Exp
genDescendBody recursiveFields = do
  -- Generate field collection expressions based on container depth
  let genFieldExpr depth var =
        if depth == 0
          then [| [ $(varE var) ] |]
          else if depth == 1
            then [| F.toList $(varE var) |]
            else do
              -- For depth > 1, use foldList to flatten nested containers
              let buildLayers 1 = varE var
                  buildLayers n = [| foldList $ F.toList $(buildLayers (n-1)) |]
              buildLayers depth

  -- Build list of field expressions
  fieldExprs <- forM recursiveFields $ \((_, typ), var) -> do
    let depth = containerDepth typ
    genFieldExpr depth var
  
  -- Combine with mconcat
  [| pure $ mconcat $(pure $ ListE fieldExprs) |]

--------------------------------------------------------------------------------

genSmartConstructors :: Name -> Q [Dec]
genSmartConstructors typeName = do
  info <- reify typeName
  validateTypeParams typeName info
  validateNoExistentials typeName info
  
  let cons = getConstructors info
  let expVar = mkName "exp"
  let fVar = mkName "f"
  
  -- Generate a smart constructor for each constructor
  mconcat <$> forM cons (\(conName, fields) -> do
    let smartName = mkName (lowerFirst (nameBase conName))
    genSmartConstructor typeName smartName conName fields fVar)

-- Helper to lowercase the first character
lowerFirst :: String -> String
lowerFirst [] = []
lowerFirst (c:cs) = toLower c : cs

-- Generate a single smart constructor
genSmartConstructor :: Name -> Name -> Name -> [BangType] -> Name -> Q [Dec]
genSmartConstructor typeName smartName conName fields fVar = do
  -- Generate parameter names
  paramVars <- forM [1..length fields] $ \i -> pure $ mkName ("a" ++ show i)
  
  -- Build the type signature
  let wrapConstraint = AppT (ConT ''Wrap) (VarT fVar)
  let returnType = AppT (VarT fVar) (ConT typeName)
  
  -- Replace exp with (f TypeName) in field types
  let paramTypes = [ replaceExpWithWrapped fVar typeName typ | (_, typ) <- fields ]
  
  let funType = ForallT [PlainTV fVar SpecifiedSpec] [wrapConstraint] $
        foldr (\paramType acc -> AppT (AppT ArrowT paramType) acc) returnType paramTypes
  
  -- Build the function body: wrap (ConName a1 a2 ...)
  let conApp = foldl AppE (ConE conName) (fmap VarE paramVars)
  let body = AppE (VarE 'wrap) conApp
  
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

genBiPlateInstance :: String -> Name -> String -> Name -> String -> Name -> Q [Dec]
genBiPlateInstance sumPrefix sumTypeName destPrefix destTypeName diffPrefix diffTypeName = do
  -- Get constructors of sum type
  sumInfo <- reify sumTypeName
  let sumCons = getConstructors sumInfo
  
  -- Get constructors of dest type
  destInfo <- reify destTypeName
  let destCons = getConstructors destInfo
  
  -- Build a map from base names to dest constructors
  let destMap = [ (baseName, (conName, fields)) 
                | (conName, fields) <- destCons
                , Just baseName <- [stripPrefix destPrefix (nameBase conName)]
                ]
  
  let unwrapVar = mkName "unwrap"
  let wrapVar = mkName "wrap"
  let fVar = mkName "f"
  let exprVar = mkName "expr"
  let innerVar = mkName "inner"
  
  -- For each sum constructor, match it to dest or diff by name
  matches <- matchSumConstructors sumPrefix sumCons destMap
    (\(sumConName, fields) (destConName, _) _ ->
      genSubsetMatch sumConName destConName fields unwrapVar wrapVar fVar
    )
    (\(sumConName, fields) baseName -> do
      let diffConName = mkName (diffPrefix ++ baseName)
      genDiffMatch sumConName diffConName fields unwrapVar wrapVar fVar
    )
 
  -- Validate that all constructors were matched
  when (length matches /= length sumCons) $
    fail $ "Not all sum constructors were matched: expected " ++ show (length sumCons) ++ " but got " ++ show (length matches)

  let transformBody = DoE Nothing
        [ BindS (VarP innerVar) (AppE (VarE unwrapVar) (VarE exprVar))
        , NoBindS (CaseE (VarE innerVar) matches)
        ]

  let transformClause = Clause 
        [VarP unwrapVar, VarP wrapVar, VarP fVar, VarP exprVar]
        (NormalB transformBody)
        []

  pure
    [ InstanceD Nothing [] 
        (AppT (AppT (AppT (ConT ''BiPlate) (ConT sumTypeName)) (ConT destTypeName)) (ConT diffTypeName))
        [FunD 'transformBiM [transformClause]]
    ]

-- For subset constructors: wrap =<< (DestCon <$> transform fields)
genSubsetMatch :: Name -> Name -> [BangType] -> Name -> Name -> Name -> Q Match
genSubsetMatch sumConName destConName fields unwrapVar wrapVar fVar = do
  fieldVars <- forM [1..length fields] $ \i -> pure $ mkName ("_a" ++ show i)
  
  let pat = ConP sumConName [] (fmap VarP fieldVars)
 
  body <- if null fields
    then [| $(varE wrapVar) =<< pure $(conE destConName) |]
    else do
      conApp <- genConstructorApp destConName fields fieldVars unwrapVar wrapVar fVar
      [| $(varE wrapVar) =<< $(pure conApp) |]

  pure $ Match pat (NormalB body) []

-- For diff constructors: f =<< (DiffCon <$> transform fields)
genDiffMatch :: Name -> Name -> [BangType] -> Name -> Name -> Name -> Q Match
genDiffMatch sumConName diffConName fields unwrapVar wrapVar fVar = do
  fieldVars <- forM [1..length fields] $ \i -> pure $ mkName ("_a" ++ show i)
  
  let pat = ConP sumConName [] (fmap VarP fieldVars)
  
  body <- if null fields
    then [| $(varE fVar) =<< pure $(conE diffConName) |]
    else do
      conApp <- genConstructorApp diffConName fields fieldVars unwrapVar wrapVar fVar
      [| $(varE fVar) =<< $(pure conApp) |]

  pure $ Match pat (NormalB body) []

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
