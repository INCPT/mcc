{-# LANGUAGE OverloadedRecordDot #-}

module OSC.AST where

import qualified Control.Monad.State as ST
import Data.Map (Map)
import qualified Data.Map as M

data Ident = Ident String
  deriving (Eq, Ord)

data Expr
 = Unit
 | Var Ident
 | LitB Bool
 | LitI Int
 | LitF Double
 | Abs Type Type [Statement] Expr
 | App Expr Expr

data SType = TBool | I32 | I64 | F32 | F64

data CType
  = TArray SType [Int]
  | TStruct (Map Ident Type)
  | TAbs Type Type

data Type = TUnit | CType CType | SType SType

data Statement
  = SBinding Ident Type Expr
  | SIf Expr [Statement] [Statement]
  | SFor Expr Expr [Statement]
  | SReturn Expr

data BindingOffset = OffsetRelToFrame Int | ReturnOffset

data Frame = Frame
  { bindingsOffsets :: Map Ident BindingOffset
  , size :: Int
  }

type MemLayout = Map Ident Frame

stypeSize TBool = 4
stypeSize I32 = 4
stypeSize I64 = 8
stypeSize F32 = 4
stypeSize F64 = 8

typeSize :: Type -> Int
typeSize TUnit = 0
typeSize (SType t) = stypeSize t
typeSize (CType (TArray t dim)) = stypeSize t * product dim
typeSize (CType (TStruct m)) = sum [ typeSize t | t <- M.elems m ]
typeSize (CType (TAbs _ _)) = 4

-- eliminate empty complex bindings, e.g. a: f32[] = b: a and b are interchangeable here (but not when they are simple)
-- complex or captured values (including simple ones) go in linear memory
-- captured values are passed as additional reference arguments to the function

inc :: Int -> ST.State Int Int
inc x = do
  prev <- ST.get
  ST.put prev
  pure (prev + x)

memLayoutE :: Expr -> ST.State Int (Maybe Frame)
memLayoutE = undefined

memLayoutS :: [Statement] -> Expr -> ST.State Int Frame
memLayoutS sts ret = undefined
  where
    returnBinding :: Maybe Ident
    returnBinding = case ret of
      Var v -> Just v
      _ -> Nothing

    a :: ST.State Int (Map Ident BindingOffset)
    a = M.fromList . concat <$> sequence
      [ case st of
          SBinding n t _
            | Just n == returnBinding -> pure [(n, ReturnOffset)]
            | otherwise -> do
                offset <- inc (typeSize t)
                pure [(n, OffsetRelToFrame offset)]
          SFor _ _ sts' -> do
            frame <- memLayoutS sts' Unit
            _ <- inc frame.size
            pure []
      | st <- sts
      ]

-- inline :: Expr -> Expr -> ParentStatementsZipper -> ParentStatementsZipper
-- inline (App (Abs TUnit rt ss r) Unit) = undefined
