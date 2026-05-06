{-# LANGUAGE OverloadedRecordDot #-}

module OSC.Codegen.Interpret where

import Control.Monad (replicateM, forM_)

import OSC.Expr.Comp
import OSC.Codegen
import qualified Data.Map as M
import Data.Map (Map)
import Control.Monad.State
import Data.Maybe (fromMaybe)

data Value = VNumber Number | VArr [Value]
  deriving Show

type VarTable = Map Location Value

zeroValue :: Type -> Value
zeroValue (TNumber TI32) = VNumber (I32 0)
zeroValue (TNumber TF32) = VNumber (F32 0)
zeroValue (TNumber TI64) = VNumber (I64 0)
zeroValue (TNumber TF64) = VNumber (F64 0)
zeroValue (TArr t dim) = VArr (replicate dim (zeroValue t))
zeroValue (TLam _ _) = VNumber (I32 0)

applyOp :: Op -> Value -> Value -> Value
applyOp Add (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (a + b))
applyOp Add (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I64 (a + b))
applyOp Add (VNumber (F32 a)) (VNumber (F32 b)) = VNumber (F32 (a + b))
applyOp Add (VNumber (F64 a)) (VNumber (F64 b)) = VNumber (F64 (a + b))
applyOp Sub (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (a - b))
applyOp Sub (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I64 (a - b))
applyOp Sub (VNumber (F32 a)) (VNumber (F32 b)) = VNumber (F32 (a - b))
applyOp Sub (VNumber (F64 a)) (VNumber (F64 b)) = VNumber (F64 (a - b))
applyOp Mul (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (a * b))
applyOp Mul (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I64 (a * b))
applyOp Mul (VNumber (F32 a)) (VNumber (F32 b)) = VNumber (F32 (a * b))
applyOp Mul (VNumber (F64 a)) (VNumber (F64 b)) = VNumber (F64 (a * b))
applyOp Div (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (a `div` b))
applyOp Div (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I64 (a `div` b))
applyOp Div (VNumber (F32 a)) (VNumber (F32 b)) = VNumber (F32 (a / b))
applyOp Div (VNumber (F64 a)) (VNumber (F64 b)) = VNumber (F64 (a / b))
applyOp Mod (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (a `mod` b))
applyOp Mod (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I64 (a `mod` b))
applyOp Eq (VNumber (I32 a)) (VNumber (I32 b)) = VNumber (I32 (if a == b then 1 else 0))
applyOp Eq (VNumber (I64 a)) (VNumber (I64 b)) = VNumber (I64 (if a == b then 1 else 0))
applyOp Eq (VNumber (F32 a)) (VNumber (F32 b)) = VNumber (I32 (if a == b then 1 else 0))
applyOp Eq (VNumber (F64 a)) (VNumber (F64 b)) = VNumber (I64 (if a == b then 1 else 0))
applyOp _ _ _ = error "applyOp: unsupported operation"
