{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.TH where

import Control.Monad (forM_)

import Language.Haskell.TH
import Control.Monad (forM, foldM)
import qualified Data.Foldable as F

foldl1M :: Monad m => (a -> a -> m a) -> [a] -> m a
foldl1M _ [] = error "foldl1M: empty list"
foldl1M _ [x] = pure x
foldl1M f (x:xs) = foldM f x xs

class Plate expr where
  descend :: Monad m
    => (forall y. mu y -> m (y (mu y)))  -- | Unrwap
 
    -> (expr (mu expr) -> m (Maybe a))   -- | Gather
    -> mu expr
    -> m [a]

class BiPlate a b c | a c -> b, b c -> a where
  transformBi :: Monad m
    => (forall y. mu y -> m (y (mu y)))      -- | Unwrap
    -> (forall y. y (mu' y) -> m (mu' y))    -- | Wrap

    -> (c (mu' b) -> m (b (mu' b)))          -- | Transform
    -> mu a
    -> m (mu' b)

-- Helper functions ------------------------------------------------------------

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

-- Check if a constructor (by fields) is in a list of constructors
consInByFields :: (Name, [BangType]) -> [(Name, [BangType])] -> Bool
consInByFields con = any (consEqualByFields con)

replaceExpType :: Name -> BangType -> BangType
replaceExpType expVar (bang, typ) = (bang, replaceInType expVar typ)

replaceInType :: Name -> Type -> Type
replaceInType expVar typ = case typ of
  AppT _ (AppT ListT innerType) -> AppT ListT (replaceInType expVar innerType)
  AppT f a -> AppT (replaceInType expVar f) (replaceInType expVar a)
  VarT _ -> VarT expVar
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

--------------------------------------------------------------------------------

makeSum :: String -> String -> [Name] -> Q [Dec]
makeSum prefix sumName typeNames = do
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
        [DerivClause Nothing [ConT ''Functor, ConT ''Foldable, ConT ''Traversable]]

  pure [sumDataDec]

makeDiff :: String -> String -> Name -> Name -> Q [Dec]
makeDiff prefix diffName sumTypeName subsetTypeName = do
  -- Get info about the sum type
  sumInfo <- reify sumTypeName
  validateTypeParams sumTypeName sumInfo
  validateNoExistentials sumTypeName sumInfo
  let allCons = getConstructors sumInfo

  -- Get info about the subset type
  subsetInfo <- reify subsetTypeName
  validateTypeParams subsetTypeName subsetInfo
  validateNoExistentials subsetTypeName subsetInfo
  let subsetCons = getConstructors subsetInfo

  -- Diff constructors = all - subset (comparing by fields only)
  let diffCons = [ c | c <- allCons, not (consInByFields c subsetCons) ]

  -- Create the diff type
  let expVar = mkName "exp"
  let diffTypeName = mkName diffName
  
  -- Build constructors for the diff type
  diffConsDecls <- forM diffCons $ \(conName, fields) -> do
    let newConName = mkName (prefix ++ nameBase conName)
    let newFields = fmap (replaceExpType expVar) fields
    pure $ NormalC newConName newFields

  -- Create the data declaration
  let diffDataDec = DataD [] diffTypeName [PlainTV expVar BndrReq] Nothing diffConsDecls []

  pure [diffDataDec]

--------------------------------------------------------------------------------

makePlateInstance :: Name -> Q [Dec]
makePlateInstance typeName = do
  info <- reify typeName
  let cons = getConstructors info
  
  let unwrapVar = mkName "unwrap"
  let extractVar = mkName "extract"
  let exprVar = mkName "expr"
  let innerVar = mkName "inner"
  let aVar = mkName "a"

  -- Build pattern matches for each constructor
  matches <- forM cons $ \(conName, fields) -> do
    makeDescendMatch conName fields unwrapVar extractVar

  let descendBody = DoE Nothing
        [ BindS (VarP innerVar) (AppE (VarE unwrapVar) (VarE exprVar))
        , BindS (VarP aVar) (AppE (VarE extractVar) (VarE innerVar))
        , NoBindS (CaseE (VarE aVar)
            [ Match (ConP 'Just [] [VarP (mkName "a'")]) 
                (NormalB (AppE (VarE 'pure) (ListE [VarE (mkName "a'")]))) []
            , Match (ConP 'Nothing [] []) 
                (NormalB (CaseE (VarE innerVar) matches)) []
            ])
        ]

  let descendClause = Clause 
        [VarP unwrapVar, VarP extractVar, VarP exprVar]
        (NormalB descendBody)
        []

  pure
    [ InstanceD Nothing [] 
        (AppT (ConT ''Plate) (ConT typeName))
        [FunD 'descend [descendClause]]
    ]

makeDescendMatch :: Name -> [BangType] -> Name -> Name -> Q Match
makeDescendMatch conName fields unwrapVar extractVar = do
  fieldVars <- forM [1..length fields] $ \i -> pure $ mkName ("_exp" ++ show i)
  
  let pat = ConP conName [] (fmap VarP fieldVars)
  
  -- Filter to only recursive fields (those containing the type variable)
  let recursiveFields = [ (f, v) | (f@(_, typ), v) <- zip fields fieldVars, isRecursiveType typ ]
  
  body <- if null recursiveFields
    then [| pure [] |]
    else makeDescendBody recursiveFields unwrapVar extractVar

  pure $ Match pat (NormalB body) []

makeDescendBody :: [((Bang, Type), Name)] -> Name -> Name -> Q Exp
makeDescendBody recursiveFields unwrapVar extractVar = do
  -- Generate unwrapping expression based on container depth
  let makeUnwrapExpr depth var =
        if depth == 0
          then [| descend $(varE unwrapVar) $(varE extractVar) $(varE var) |]
          else if depth == 1
            then [| (fmap mconcat . traverse (descend $(varE unwrapVar) $(varE extractVar))) (F.toList $(varE var)) |]
            else do
              -- For depth > 1, we need to stack: mconcat $ F.toList $ sequenceA $ F.toList
              -- Build from the inside out
              let buildLayers 0 = varE var
                  buildLayers n = [| mconcat $ F.toList $ sequenceA $ F.toList $(buildLayers (n-1)) |]
              [| (fmap mconcat . traverse (descend $(varE unwrapVar) $(varE extractVar))) $(buildLayers (depth - 1)) |]

  case recursiveFields of
    [] -> error "recursiveFields"
    [((_, typ), var)] -> do
       let depth = containerDepth typ
       makeUnwrapExpr depth var
    _ -> do
      -- Multiple fields: combine with <> using liftA2
      exprs <- forM recursiveFields $ \((_, typ), var) -> do
        let depth = containerDepth typ
        makeUnwrapExpr depth var
      
      let combineExprs a b = [| liftA2 (<>) $(pure a) $(pure b) |]
      foldl1M combineExprs exprs

--------------------------------------------------------------------------------

makeBiPlateInstance :: String -> Name -> Name -> Name -> [(Name, [BangType])] -> Q Dec
makeBiPlateInstance prefix sourceTypeName destTypeName commonTypeName sourceCons = do
  -- Get constructors of common type
  commonInfo <- reify commonTypeName
  let commonCons = getConstructors commonInfo
  
  -- Determine which constructors are in common vs diff
  let diffCons = [ c | c <- sourceCons, c `notElem` commonCons ]
  
  let unwrapVar = mkName "unwrap"
  let wrapVar = mkName "wrap"
  let fVar = mkName "f"
  let exprVar = mkName "expr"
  let innerVar = mkName "inner"

  -- Determine if this is a self-instance (source == dest == common)
  let isSelfInstance = sourceTypeName == destTypeName && destTypeName == commonTypeName

  -- Create matches for common constructors (direct mapping to dest type)
  commonMatches <- forM commonCons $ \(conName, fields) -> do
    let sourceConName = mkName (prefix ++ nameBase conName)
    let mode = if isSelfInstance then ApplyF else NoApplyF
    makeTransformMatch sourceConName conName fields unwrapVar wrapVar fVar mode

  -- Create matches for diff constructors (apply f)
  diffMatches <- forM diffCons $ \(conName, fields) -> do
    let sourceConName = mkName (prefix ++ nameBase conName)
    let diffConName = mkName (prefix ++ nameBase conName)
    makeTransformMatchDiff sourceConName diffConName fields unwrapVar wrapVar fVar

  let transformBody = DoE Nothing
        [ BindS (VarP innerVar) (AppE (VarE unwrapVar) (VarE exprVar))
        , NoBindS (CaseE (VarE innerVar) (commonMatches ++ diffMatches))
        ]

  let transformClause = Clause 
        [VarP unwrapVar, VarP wrapVar, VarP fVar, VarP exprVar]
        (NormalB transformBody)
        []

  -- Determine the third type parameter for BiPlate instance
  let thirdType = if isSelfInstance then sourceTypeName else commonTypeName

  pure $ InstanceD Nothing [] 
     (AppT (AppT (AppT (ConT ''BiPlate) (ConT sourceTypeName)) (ConT destTypeName)) (ConT thirdType))
     [FunD 'transformBi [transformClause]]

data TransformMode = ApplyF | NoApplyF | ApplyFAfter

makeTransformMatch :: Name -> Name -> [BangType] -> Name -> Name -> Name -> TransformMode -> Q Match
makeTransformMatch patConName targetConName fields unwrapVar wrapVar fVar mode = do
  fieldVars <- forM [1..length fields] $ \i -> pure $ mkName ("_a" ++ show i)
  
  let pat = ConP patConName [] (fmap VarP fieldVars)
  
  body <- makeTransformBody targetConName fields fieldVars unwrapVar wrapVar fVar mode

  pure $ Match pat (NormalB body) []

makeTransformBody :: Name -> [BangType] -> [Name] -> Name -> Name -> Name -> TransformMode -> Q Exp
makeTransformBody targetConName fields fieldVars unwrapVar wrapVar fVar mode = do
  if null fields
    then case mode of
      ApplyF -> [| $(varE wrapVar) =<< $(varE fVar) =<< pure $(conE targetConName) |]
      NoApplyF -> [| $(varE wrapVar) =<< pure $(conE targetConName) |]
      ApplyFAfter -> [| $(varE wrapVar) =<< $(varE fVar) =<< pure $(conE targetConName) |]
    else do
      -- Transform each field
      transformedFields <- forM (zip fields fieldVars) $ \((bang, typ), var) ->
        if isRecursiveType typ
          then case typ of
            AppT _ _ -> 
              -- Any container type (Maybe, [], etc.) - use traverse
              [| traverse (transformBi $(varE unwrapVar) $(varE wrapVar) $(varE fVar)) $(varE var) |]
            _ -> 
              -- Direct recursive type
              [| transformBi $(varE unwrapVar) $(varE wrapVar) $(varE fVar) $(varE var) |]
          else
            -- Non-recursive field, just return as-is
            varE var

      conApp <- foldr (\acc field -> appE (pure acc) field) (conE targetConName) (transformedFields)
      
      case mode of
        ApplyF -> [| $(varE wrapVar) =<< $(varE fVar) =<< $(pure conApp) |]
        NoApplyF -> [| $(varE wrapVar) =<< $(pure conApp) |]
        ApplyFAfter -> [| $(varE wrapVar) =<< $(varE fVar) =<< $(pure conApp) |]

makeTransformMatchDirect :: Name -> Name -> [BangType] -> Name -> Name -> Name -> Q Match
makeTransformMatchDirect sumConName targetConName fields unwrapVar wrapVar fVar =
  makeTransformMatch sumConName targetConName fields unwrapVar wrapVar fVar NoApplyF

makeTransformMatchDiff :: Name -> Name -> [BangType] -> Name -> Name -> Name -> Q Match
makeTransformMatchDiff sumConName diffConName fields unwrapVar wrapVar fVar =
  makeTransformMatch sumConName diffConName fields unwrapVar wrapVar fVar ApplyFAfter
