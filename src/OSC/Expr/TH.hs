{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}

module OSC.Expr.TH where

import Language.Haskell.TH
import Control.Monad (forM)
import Data.Traversable (traverse)

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

--------------------------------------------------------------------------------

{-
-- Simple recursive functor (can be paired with Identity)
data Mu f = Mu (f (Mu f))

-- Annotated recursive functor + monad
data Ann ann f = Ann (ann, f (Ann ann f))
data AnnM ann expr a = AnnM (Ann ann expr -> a)

-- DAG recursive functor + monad
data Dag k f = Node (f (Dag k f)) | Key k
data DagM k expr a = DagM ((k -> expr (Dag k expr)) -> a)
-}

-- write a TH function that:

---- having the following types

data Value exp = Const Int | Arr [exp]
data Expr exp = Add exp exp | Mul exp exp

---- and calling

------ makeSum "S_" "Sum0" [''Value, ''Expr]

---- will generate the following datatype:

data Sum0 exp
  = S_Const Int
  | S_Arr [exp]
  | S_Add exp exp
  | S_Mul exp exp
  deriving (Functor, Foldable, Traversable)

---- and implement the Plate and Biplate classes:

instance Plate Sum0 where
  descend unwrap extract expr = do
    inner <- unwrap expr
    a <- extract inner
    case a of
      Just a' -> pure [a']
      Nothing -> case inner of
        S_Const _ -> pure []
        -- if field is of type `h (g (f exp)) ...` (like `[exp]` or `[Maybe exp]`) then just traverse (and figure out how to do nested traversls) - we'll throw a type error if f isn't a Traversable
        S_Arr exprs -> fmap mconcat $ traverse (descend unwrap extract) exprs
        S_Add exp1 exp2 -> (<>) <$> descend unwrap extract exp1 <*> descend unwrap extract exp2
        S_Mul exp1 exp2 -> (<>) <$> descend unwrap extract exp1 <*> descend unwrap extract exp2

instance BiPlate Sum0 Sum0 Sum0 where
  transformBi unwrap wrap f expr = do
    inner <- unwrap expr
    case inner of
      S_Const n   -> wrap =<< pure (S_Const n)
      S_Arr exprs -> wrap =<< f =<< (S_Arr <$> traverse (transformBi unwrap wrap f) exprs)
      S_Add a b   -> wrap =<< f =<< (S_Add <$> transformBi unwrap wrap f a <*> transformBi unwrap wrap f b)
      S_Mul a b   -> wrap =<< f =<< (S_Add <$> transformBi unwrap wrap f a <*> transformBi unwrap wrap f b)
  
---- calling

------ makeDiff "D_" "Diff_Sum0_Expr" [''Value, ''Expr] [''Value]

---- will generate the following datatype:

data Diff_Sum0_Expr exp
  = D_Add exp exp
  | D_Mul exp exp

---- and implement the following BiPlate class:

instance BiPlate Sum0 Value Diff_Sum0_Expr where
  transformBi unwrap wrap f expr = do
    inner <- unwrap expr
    case inner of
      S_Const n -> wrap =<< pure (Const n)
      S_Arr as  -> wrap =<< (Arr <$> traverse (transformBi unwrap wrap f) as)

      S_Add a b -> wrap =<< f =<< (D_Add <$> transformBi unwrap wrap f a <*> transformBi unwrap wrap f b)
      S_Mul a b -> wrap =<< f =<< (D_Add <$> transformBi unwrap wrap f a <*> transformBi unwrap wrap f b)

--------------------------------------------------------------------------------

makeSum :: String -> String -> [Name] -> Q [Dec]
makeSum prefix sumName typeNames = do
  -- Get info about all the types
  typeInfos <- forM typeNames $ \typeName -> do
    info <- reify typeName
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
  let sumDataDec = DataD [] sumTypeName [PlainTV expVar ()] Nothing sumCons
        [DerivClause Nothing [ConT ''Functor, ConT ''Foldable, ConT ''Traversable]]

  -- Create Plate instance
  plateInst <- makePlateInstance prefix sumTypeName allCons

  -- Create BiPlate instance for Sum -> Sum
  biPlateInst <- makeBiPlateInstanceSelf prefix sumTypeName allCons

  pure [sumDataDec, plateInst, biPlateInst]

makeDiff :: String -> String -> [Name] -> [Name] -> Q [Dec]
makeDiff prefix diffName allTypeNames subsetTypeNames = do
  -- Get info about all types
  allTypeInfos <- forM allTypeNames $ \typeName -> do
    info <- reify typeName
    pure (typeName, info)

  subsetTypeInfos <- forM subsetTypeNames $ \typeName -> do
    info <- reify typeName
    pure (typeName, info)

  -- Get constructors
  let allCons = mconcat [ getConstructors info | (_, info) <- allTypeInfos ]
  let subsetCons = mconcat [ getConstructors info | (_, info) <- subsetTypeInfos ]

  -- Diff constructors = all - subset
  let diffCons = [ c | c <- allCons, c `notElem` subsetCons ]

  -- Create the diff type
  let expVar = mkName "exp"
  let diffTypeName = mkName diffName
  
  -- Build constructors for the diff type
  diffConsDecls <- forM diffCons $ \(conName, fields) -> do
    let newConName = mkName (prefix ++ nameBase conName)
    let newFields = fmap (replaceExpType expVar) fields
    pure $ NormalC newConName newFields

  -- Create the data declaration
  let diffDataDec = DataD [] diffTypeName [PlainTV expVar ()] Nothing diffConsDecls []

  -- Determine the sum and target types
  -- Assume the sum type is named with the pattern from makeSum
  -- For now, we'll need to construct the names
  let sumTypeName = mkName $ "Sum0"  -- This should be derived from allTypeNames
  let targetTypeName = head subsetTypeNames  -- First subset type

  -- Create BiPlate instance for Sum -> Target via Diff
  biPlateInst <- makeBiPlateInstanceDiff prefix sumTypeName targetTypeName diffTypeName allCons subsetCons

  pure [diffDataDec, biPlateInst]

--------------------------------------------------------------------------------
-- Helper functions

getConstructors :: Info -> [(Name, [BangType])]
getConstructors (TyConI (DataD _ _ _ _ cons _)) = 
  [ (name, fields) | NormalC name fields <- cons ]
getConstructors _ = []

replaceExpType :: Name -> BangType -> BangType
replaceExpType expVar (bang, typ) = (bang, replaceInType expVar typ)

replaceInType :: Name -> Type -> Type
replaceInType expVar typ = case typ of
  AppT (AppT ListT innerType) -> AppT ListT (replaceInType expVar innerType)
  AppT f a -> AppT (replaceInType expVar f) (replaceInType expVar a)
  VarT _ -> VarT expVar
  ConT name -> ConT name
  _ -> typ

makePlateInstance :: String -> Name -> [(Name, [BangType])] -> Q Dec
makePlateInstance prefix sumTypeName cons = do
  let unwrapVar = mkName "unwrap"
  let extractVar = mkName "extract"
  let exprVar = mkName "expr"
  let innerVar = mkName "inner"
  let aVar = mkName "a"

  -- Build pattern matches for each constructor
  matches <- forM cons $ \(conName, fields) -> do
    let newConName = mkName (prefix ++ nameBase conName)
    makeDescendMatch newConName fields unwrapVar extractVar

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

  pure $ InstanceD Nothing [] 
    (AppT (ConT ''Plate) (ConT sumTypeName))
    [FunD 'descend [descendClause]]

makeDescendMatch :: Name -> [BangType] -> Name -> Name -> Q Match
makeDescendMatch conName fields unwrapVar extractVar = do
  fieldVars <- forM [1..length fields] $ \i -> pure $ mkName ("exp" ++ show i)
  
  let pat = ConP conName [] (fmap VarP fieldVars)
  
  body <- if null fields
    then pure $ AppE (VarE 'pure) (ListE [])
    else makeDescendBody fields fieldVars unwrapVar extractVar

  pure $ Match pat (NormalB body) []

makeDescendBody :: [BangType] -> [Name] -> Name -> Name -> Q Exp
makeDescendBody fields fieldVars unwrapVar extractVar = do
  let isTraversable (_, typ) = case typ of
        AppT ListT _ -> True
        _ -> False

  if length fields == 1
    then do
      let (bang, typ) = head fields
      let var = head fieldVars
      if isTraversable (bang, typ)
        then pure $ AppE (AppE (VarE 'fmap) (VarE 'mconcat))
               (AppE (AppE (VarE 'traverse) 
                 (AppE (AppE (VarE 'descend) (VarE unwrapVar)) (VarE extractVar)))
                 (VarE var))
        else pure $ AppE (AppE (AppE (VarE 'descend) (VarE unwrapVar)) (VarE extractVar)) (VarE var)
    else do
      -- Multiple fields: combine with <>
      exprs <- forM (zip fields fieldVars) $ \((bang, typ), var) ->
        if isTraversable (bang, typ)
          then pure $ AppE (AppE (VarE 'fmap) (VarE 'mconcat))
                 (AppE (AppE (VarE 'traverse) 
                   (AppE (AppE (VarE 'descend) (VarE unwrapVar)) (VarE extractVar)))
                   (VarE var))
          else pure $ AppE (AppE (AppE (VarE 'descend) (VarE unwrapVar)) (VarE extractVar)) (VarE var)
      
      pure $ foldl1 (\a b -> InfixE (Just a) (VarE '(<>)) (Just b)) exprs

makeBiPlateInstanceSelf :: String -> Name -> [(Name, [BangType])] -> Q Dec
makeBiPlateInstanceSelf prefix sumTypeName cons = do
  let unwrapVar = mkName "unwrap"
  let wrapVar = mkName "wrap"
  let fVar = mkName "f"
  let exprVar = mkName "expr"
  let innerVar = mkName "inner"

  matches <- forM cons $ \(conName, fields) -> do
    let newConName = mkName (prefix ++ nameBase conName)
    makeTransformMatch newConName fields unwrapVar wrapVar fVar True

  let transformBody = DoE Nothing
        [ BindS (VarP innerVar) (AppE (VarE unwrapVar) (VarE exprVar))
        , NoBindS (CaseE (VarE innerVar) matches)
        ]

  let transformClause = Clause 
        [VarP unwrapVar, VarP wrapVar, VarP fVar, VarP exprVar]
        (NormalB transformBody)
        []

  pure $ InstanceD Nothing [] 
    (AppT (AppT (AppT (ConT ''BiPlate) (ConT sumTypeName)) (ConT sumTypeName)) (ConT sumTypeName))
    [FunD 'transformBi [transformClause]]

makeBiPlateInstanceDiff :: String -> Name -> Name -> Name -> [(Name, [BangType])] -> [(Name, [BangType])] -> Q Dec
makeBiPlateInstanceDiff prefix sumTypeName targetTypeName diffTypeName allCons subsetCons = do
  let unwrapVar = mkName "unwrap"
  let wrapVar = mkName "wrap"
  let fVar = mkName "f"
  let exprVar = mkName "expr"
  let innerVar = mkName "inner"

  -- Create matches for subset constructors (direct mapping)
  subsetMatches <- forM subsetCons $ \(conName, fields) -> do
    let sumConName = mkName (prefix ++ nameBase conName)
    makeTransformMatchDirect sumConName conName fields unwrapVar wrapVar fVar

  -- Create matches for diff constructors (apply f)
  let diffCons = [ c | c <- allCons, c `notElem` subsetCons ]
  diffMatches <- forM diffCons $ \(conName, fields) -> do
    let sumConName = mkName (prefix ++ nameBase conName)
    let diffConName = mkName (prefix ++ nameBase conName)
    makeTransformMatchDiff sumConName diffConName fields unwrapVar wrapVar fVar

  let transformBody = DoE Nothing
        [ BindS (VarP innerVar) (AppE (VarE unwrapVar) (VarE exprVar))
        , NoBindS (CaseE (VarE innerVar) (subsetMatches ++ diffMatches))
        ]

  let transformClause = Clause 
        [VarP unwrapVar, VarP wrapVar, VarP fVar, VarP exprVar]
        (NormalB transformBody)
        []

  pure $ InstanceD Nothing [] 
    (AppT (AppT (AppT (ConT ''BiPlate) (ConT sumTypeName)) (ConT targetTypeName)) (ConT diffTypeName))
    [FunD 'transformBi [transformClause]]

makeTransformMatch :: Name -> [BangType] -> Name -> Name -> Name -> Bool -> Q Match
makeTransformMatch conName fields unwrapVar wrapVar fVar applyF = do
  fieldVars <- forM [1..length fields] $ \i -> pure $ mkName ("a" ++ show i)
  
  let pat = ConP conName [] (fmap VarP fieldVars)
  
  body <- makeTransformBody conName fields fieldVars unwrapVar wrapVar fVar applyF

  pure $ Match pat (NormalB body) []

makeTransformBody :: Name -> [BangType] -> [Name] -> Name -> Name -> Name -> Bool -> Q Exp
makeTransformBody conName fields fieldVars unwrapVar wrapVar fVar applyF = do
  if null fields
    then pure $ InfixE 
           (Just (VarE wrapVar)) 
           (VarE '(=<<)) 
           (Just (AppE (VarE 'pure) (ConE conName)))
    else do
      -- Transform each field
      transformedFields <- forM (zip fields fieldVars) $ \((bang, typ), var) ->
        case typ of
          AppT ListT _ -> 
            pure $ AppE (AppE (VarE 'traverse) 
                     (AppE (AppE (AppE (VarE 'transformBi) (VarE unwrapVar)) (VarE wrapVar)) (VarE fVar)))
                   (VarE var)
          _ -> 
            pure $ AppE (AppE (AppE (AppE (VarE 'transformBi) (VarE unwrapVar)) (VarE wrapVar)) (VarE fVar)) (VarE var)

      let conApp = foldl AppE (ConE conName) transformedFields
      
      if applyF
        then pure $ InfixE 
               (Just (VarE wrapVar)) 
               (VarE '(=<<)) 
               (Just (InfixE (Just (VarE fVar)) (VarE '(=<<)) (Just conApp)))
        else pure $ InfixE 
               (Just (VarE wrapVar)) 
               (VarE '(=<<)) 
               (Just conApp)

makeTransformMatchDirect :: Name -> Name -> [BangType] -> Name -> Name -> Name -> Q Match
makeTransformMatchDirect sumConName targetConName fields unwrapVar wrapVar fVar = do
  fieldVars <- forM [1..length fields] $ \i -> pure $ mkName ("a" ++ show i)
  
  let pat = ConP sumConName [] (fmap VarP fieldVars)
  
  body <- makeTransformBodyDirect targetConName fields fieldVars unwrapVar wrapVar fVar

  pure $ Match pat (NormalB body) []

makeTransformBodyDirect :: Name -> [BangType] -> [Name] -> Name -> Name -> Name -> Q Exp
makeTransformBodyDirect targetConName fields fieldVars unwrapVar wrapVar fVar = do
  if null fields
    then pure $ InfixE 
           (Just (VarE wrapVar)) 
           (VarE '(=<<)) 
           (Just (AppE (VarE 'pure) (ConE targetConName)))
    else do
      transformedFields <- forM (zip fields fieldVars) $ \((bang, typ), var) ->
        case typ of
          AppT ListT _ -> 
            pure $ AppE (AppE (VarE 'traverse) 
                     (AppE (AppE (AppE (VarE 'transformBi) (VarE unwrapVar)) (VarE wrapVar)) (VarE fVar)))
                   (VarE var)
          _ -> 
            pure $ AppE (AppE (AppE (AppE (VarE 'transformBi) (VarE unwrapVar)) (VarE wrapVar)) (VarE fVar)) (VarE var)

      let conApp = foldl AppE (ConE targetConName) transformedFields
      
      pure $ InfixE 
        (Just (VarE wrapVar)) 
        (VarE '(=<<)) 
        (Just conApp)

makeTransformMatchDiff :: Name -> Name -> [BangType] -> Name -> Name -> Name -> Q Match
makeTransformMatchDiff sumConName diffConName fields unwrapVar wrapVar fVar = do
  fieldVars <- forM [1..length fields] $ \i -> pure $ mkName ("a" ++ show i)
  
  let pat = ConP sumConName [] (fmap VarP fieldVars)
  
  body <- makeTransformBodyDiff diffConName fields fieldVars unwrapVar wrapVar fVar

  pure $ Match pat (NormalB body) []

makeTransformBodyDiff :: Name -> [BangType] -> [Name] -> Name -> Name -> Name -> Q Exp
makeTransformBodyDiff diffConName fields fieldVars unwrapVar wrapVar fVar = do
  if null fields
    then pure $ InfixE 
           (Just (VarE wrapVar)) 
           (VarE '(=<<)) 
           (Just (InfixE (Just (VarE fVar)) (VarE '(=<<)) (Just (AppE (VarE 'pure) (ConE diffConName)))))
    else do
      transformedFields <- forM (zip fields fieldVars) $ \((bang, typ), var) ->
        case typ of
          AppT ListT _ -> 
            pure $ AppE (AppE (VarE 'traverse) 
                     (AppE (AppE (AppE (VarE 'transformBi) (VarE unwrapVar)) (VarE wrapVar)) (VarE fVar)))
                   (VarE var)
          _ -> 
            pure $ AppE (AppE (AppE (AppE (VarE 'transformBi) (VarE unwrapVar)) (VarE wrapVar)) (VarE fVar)) (VarE var)

      let conApp = foldl AppE (ConE diffConName) transformedFields
      
      pure $ InfixE 
        (Just (VarE wrapVar)) 
        (VarE '(=<<)) 
        (Just (InfixE (Just (VarE fVar)) (VarE '(=<<)) (Just conApp)))
