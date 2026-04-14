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
import Control.Monad (forM, foldM)
import Data.Traversable (traverse)

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

------ makeDiff "D_" "Diff_Sum0_Expr" ''Sum0 ''Value

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
  let sumDataDec = DataD [] sumTypeName [PlainTV expVar undefined] Nothing sumCons
        [DerivClause Nothing [ConT ''Functor, ConT ''Foldable, ConT ''Traversable]]

  -- Create Plate instance
  plateInst <- makePlateInstance prefix sumTypeName allCons

  -- Create BiPlate instance for Sum -> Sum (self-instance)
  biPlateInst <- makeBiPlateInstance prefix sumTypeName sumTypeName sumTypeName allCons

  pure [sumDataDec, plateInst, biPlateInst]

makeDiff :: String -> String -> Name -> Name -> Q [Dec]
makeDiff prefix diffName sumTypeName subsetTypeName = do
  -- Get info about the sum type and subset type
  sumInfo <- reify sumTypeName
  subsetInfo <- reify subsetTypeName

  -- Get constructors
  let allCons = getConstructors sumInfo
  let subsetCons = getConstructors subsetInfo

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
  let diffDataDec = DataD [] diffTypeName [PlainTV expVar undefined] Nothing diffConsDecls []

  -- Create BiPlate instance for Sum -> Subset via Diff
  biPlateInst <- makeBiPlateInstance prefix sumTypeName subsetTypeName diffTypeName allCons

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
  AppT _ (AppT ListT innerType) -> AppT ListT (replaceInType expVar innerType)
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
    then [| pure [] |]
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
        then [| fmap mconcat $ traverse (descend $(varE unwrapVar) $(varE extractVar)) $(varE var) |]
        else [| descend $(varE unwrapVar) $(varE extractVar) $(varE var) |]
    else do
      -- Multiple fields: combine with <>
      exprs <- forM (zip fields fieldVars) $ \((bang, typ), var) ->
        if isTraversable (bang, typ)
          then [| fmap mconcat $ traverse (descend $(varE unwrapVar) $(varE extractVar)) $(varE var) |]
          else [| descend $(varE unwrapVar) $(varE extractVar) $(varE var) |]
      
      let combineExprs a b = [| $(pure a) <> $(pure b) |]
      foldl1M combineExprs exprs

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
  fieldVars <- forM [1..length fields] $ \i -> pure $ mkName ("a" ++ show i)
  
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
        case typ of
          AppT ListT _ -> 
            [| traverse (transformBi $(varE unwrapVar) $(varE wrapVar) $(varE fVar)) $(varE var) |]
          _ -> 
            [| transformBi $(varE unwrapVar) $(varE wrapVar) $(varE fVar) $(varE var) |]

      conApp <- foldM (\acc field -> appE acc field) (conE targetConName) transformedFields
      
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
