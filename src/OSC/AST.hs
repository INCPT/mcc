module OSC.AST where

import Data.Map (Map)

data Ident

data Expr

data Type = CType CType | SType SType

data CType
  = Array SType [Int]
  | Structure (Map Ident Type)
  | Fun [Type] Type

data SType = I32 | I64 | F32 | F64

data Statement
  = CBindInit Ident CType Expr
  | SBindInit Ident SType Expr
  | SBindAssign Ident SType Expr

data Abs
  = AbsE Type Type Expr
  | AbsS Type Type [Statement]

data MemLocation

data ReturnMem = SReturn | CReturn MemLocation

-- logic
-- simple types: use wasm calling convention
-- complex types
