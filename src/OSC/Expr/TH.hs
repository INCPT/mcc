{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.TH where

import Control.Monad (forM_, unless, when)

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

{-# INLINE foldMapM #-}
foldMapM :: Applicative f => Monoid b => (a -> f b) -> [a] -> f b
foldMapM f = fmap mconcat . traverse f

{-# INLINE foldList #-}
foldList :: Foldable t => Applicative t => [t a] -> [a]
foldList = mconcat . F.toList . sequenceA

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
            then [| foldMapM (descend $(varE unwrapVar) $(varE extractVar)) (F.toList $(varE var)) |]
            else do
              -- For depth > 1, use foldList to flatten nested containers
              let buildLayers 0 = varE var
                  buildLayers n = [| foldList $ F.toList $(buildLayers (n-1)) |]
              [| foldMapM (descend $(varE unwrapVar) $(varE extractVar)) $(buildLayers (depth - 1)) |]

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

makeBiPlateInstance :: String -> Name -> String -> Name -> String -> Name -> Q [Dec]
makeBiPlateInstance sumPrefix sumTypeName destPrefix destTypeName diffPrefix diffTypeName = do
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
  matches <- forM sumCons $ \sumCon@(sumConName, fields) -> do
    let sumName = nameBase sumConName
    
    -- Try to strip sum prefix to get base name
    case stripPrefix sumPrefix sumName of
      Nothing -> fail $ "Sum constructor " ++ sumName ++ " doesn't have expected prefix " ++ sumPrefix
      Just baseName -> do
        -- Check if this base name exists in dest constructors
        case lookup baseName destMap of
          Just (destConName, destFields) -> do
            -- Validate that fields match
            unless (consEqualByFields sumCon (destConName, destFields)) $
              fail $ "Constructor " ++ sumName ++ " has different fields than dest constructor " ++ nameBase destConName
            makeSubsetMatch sumConName destConName fields unwrapVar wrapVar fVar
          Nothing -> do
            -- Must be a diff constructor
            let diffConName = mkName (diffPrefix ++ baseName)
            makeDiffMatch sumConName diffConName fields unwrapVar wrapVar fVar
  
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
        [FunD 'transformBi [transformClause]]
    ]

-- For subset constructors: wrap =<< (DestCon <$> transform fields)
makeSubsetMatch :: Name -> Name -> [BangType] -> Name -> Name -> Name -> Q Match
makeSubsetMatch sumConName destConName fields unwrapVar wrapVar fVar = do
  fieldVars <- forM [1..length fields] $ \i -> pure $ mkName ("_a" ++ show i)
  
  let pat = ConP sumConName [] (fmap VarP fieldVars)
 
  body <- if null fields
    then [| $(varE wrapVar) =<< pure $(conE destConName) |]
    else do
      transformedFields <- forM (zip fields fieldVars) $ \((_, typ), var) ->
        makeFieldTransform typ var unwrapVar wrapVar fVar
      
      -- Build the constructor application using <$> and <*>
      let destCon = conE destConName
      conApp <- case transformedFields of
        [] -> error "impossible: null fields already handled"
        [field] -> [| $(destCon) <$> $(pure field) |]
        (field:rest) -> do
          initial <- [| $(destCon) <$> $(pure field) |]
          foldM (\acc f -> [| $(pure acc) <*> $(pure f) |]) initial rest
      
      [| $(varE wrapVar) =<< $(pure conApp) |]

  pure $ Match pat (NormalB body) []

-- For diff constructors: wrap =<< f =<< (DiffCon <$> transform fields)
makeDiffMatch :: Name -> Name -> [BangType] -> Name -> Name -> Name -> Q Match
makeDiffMatch sumConName diffConName fields unwrapVar wrapVar fVar = do
  fieldVars <- forM [1..length fields] $ \i -> pure $ mkName ("_a" ++ show i)
  
  let pat = ConP sumConName [] (fmap VarP fieldVars)
  
  body <- if null fields
    then [| $(varE wrapVar) =<< $(varE fVar) =<< pure $(conE diffConName) |]
    else do
      transformedFields <- forM (zip fields fieldVars) $ \((_, typ), var) ->
        makeFieldTransform typ var unwrapVar wrapVar fVar
      
      -- Build the constructor application using <$> and <*>
      let diffCon = conE diffConName
      conApp <- case transformedFields of
        [] -> error "impossible: null fields already handled"
        [field] -> [| $(diffCon) <$> $(pure field) |]
        (field:rest) -> do
          initial <- [| $(diffCon) <$> $(pure field) |]
          foldM (\acc f -> [| $(pure acc) <*> $(pure f) |]) initial rest
      
      [| $(varE wrapVar) =<< $(varE fVar) =<< $(pure conApp) |]

  pure $ Match pat (NormalB body) []

-- Transform a field based on its type structure
makeFieldTransform :: Type -> Name -> Name -> Name -> Name -> Q Exp
makeFieldTransform typ var unwrapVar wrapVar fVar
  | not (isRecursiveType typ) = [| pure $(varE var) |]  -- Non-recursive: wrap in pure
  | otherwise = case typ of
      VarT _ -> 
        -- Direct recursive: transformBi unwrap wrap f var
        [| transformBi $(varE unwrapVar) $(varE wrapVar) $(varE fVar) $(varE var) |]
      AppT _ _ ->
        -- Container: traverse (transformBi unwrap wrap f) var
        -- Handle nested containers by counting depth
        let depth = containerDepth typ
        in if depth == 1
          then [| traverse (transformBi $(varE unwrapVar) $(varE wrapVar) $(varE fVar)) $(varE var) |]
          else makeNestedTraverse depth var unwrapVar wrapVar fVar
      _ -> varE var

-- Handle nested containers like Maybe (Either String [exp])
makeNestedTraverse :: Int -> Name -> Name -> Name -> Name -> Q Exp
makeNestedTraverse depth var unwrapVar wrapVar fVar =
  [| (traverse $(buildTraverse (depth - 1))) $(varE var) |]
  where
    buildTraverse 0 = [| transformBi $(varE unwrapVar) $(varE wrapVar) $(varE fVar) |]
    buildTraverse n = [| traverse $(buildTraverse (n - 1)) |]
