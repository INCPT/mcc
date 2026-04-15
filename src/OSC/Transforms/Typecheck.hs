{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module OSC.Transforms.Typecheck where

import Control.Monad.Trans.Class (lift)
import qualified Control.Monad.Reader as R
import qualified Control.Monad.Except as E

import Data.Map (Map)
import qualified Data.Map as M

import OSC.Expr.Plate (transform)
import OSC.Expr.Functors
import OSC.Expr.TH
import OSC.Expr.Base (TNumber (..), Type (..), Op (..))
import qualified OSC.Expr.Base as B

$(makeSum "" "Exp" [''B.Exp, ''B.Lam, ''B.Select, ''B.Rec])
$(makeBiPlateInstance "" ''Exp "" ''Exp "" ''Empty)

--------------------------------------------------------------------------------

data TypeError pos
  = BinOpTypeMismatch pos pos Op Type Type
  | BinOpInvalidTypes pos pos Op Type Type
  | EmptyArray pos
  | ArrayElementTypeMismatch pos [Type]
  | UnknownBinding pos B.Ident
  | FunctionReturnTypeMismatch pos Type Type
  | ArgumentCountMismatch pos Int Int
  | ArgumentTypeMismatch pos Int Type Type
  | NotAnArray pos Type
  | InvalidIndexType pos Type
  | RecDelayNotPositive pos Int
  | RecTypeContainsFunction pos Type
  | RecReturnTypeMismatch pos Type Type
  | DuplicateBindings pos [B.Ident]
  | CyclicDependency pos [B.Ident]
  deriving Show

type ExpA ann = Ann ann Exp
type TypecheckM pos = AnnM pos (E.ExceptT (TypeError pos) (R.Reader (Map B.Ident Type)))

typecheck :: ExpA pos -> TypecheckM pos (ExpA (pos, Type))
typecheck = transform (\(Ann (ann, f)) -> R.local (const ann) (pure f)) f
  where
    f :: Exp (ExpA (pos, Type)) -> TypecheckM pos (ExpA (pos, Type))
    f (Const n) = R.ask >>= \pos -> pure $ Ann ((pos, B.numberType n), Const n)
    
    f (Op op a@(Ann ((apos, at), _)) b@(Ann ((bpos, bt), _))) = case (op, at, bt) of
      -- Arithmetic operations: return same type as operands
      (B.Add, TNumber t, TNumber u) | t == u -> flowAnn (,TNumber t) $ pure $ Op op a b
      (B.Sub, TNumber t, TNumber u) | t == u -> flowAnn (,TNumber t) $ pure $ Op op a b
      (B.Mul, TNumber t, TNumber u) | t == u -> flowAnn (,TNumber t) $ pure $ Op op a b
      (B.Div, TNumber t, TNumber u) | t == u -> flowAnn (,TNumber t) $ pure $ Op op a b
      (B.Mod, TNumber t, TNumber u) | t == u -> flowAnn (,TNumber t) $ pure $ Op op a b
      (B.Rem, TNumber t, TNumber u) | t == u -> flowAnn (,TNumber t) $ pure $ Op op a b
      (B.Min, TNumber t, TNumber u) | t == u -> flowAnn (,TNumber t) $ pure $ Op op a b
      (B.Max, TNumber t, TNumber u) | t == u -> flowAnn (,TNumber t) $ pure $ Op op a b
      (B.CopySign, TNumber t, TNumber u) | t == u -> flowAnn (,TNumber t) $ pure $ Op op a b
      
      -- Bitwise operations: integer types only
      (B.And, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> flowAnn (,TNumber t) $ pure $ Op op a b
      (B.Or, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> flowAnn (,TNumber t) $ pure $ Op op a b
      (B.Xor, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> flowAnn (,TNumber t) $ pure $ Op op a b
      (B.Shl, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> flowAnn (,TNumber t) $ pure $ Op op a b
      (B.Shr, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> flowAnn (,TNumber t) $ pure $ Op op a b
      (B.Rotl, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> flowAnn (,TNumber t) $ pure $ Op op a b
      (B.Rotr, TNumber t, TNumber u) | t == u && (t == TI32 || t == TI64) -> flowAnn (,TNumber t) $ pure $ Op op a b
      
      -- Comparison operations: return I32 (boolean)
      (B.Eq, TNumber t, TNumber u) | t == u -> flowAnn (,TNumber TI32) $ pure $ Op op a b
      (B.Ne, TNumber t, TNumber u) | t == u -> flowAnn (,TNumber TI32) $ pure $ Op op a b
      (B.Gt, TNumber t, TNumber u) | t == u -> flowAnn (,TNumber TI32) $ pure $ Op op a b
      (B.Lt, TNumber t, TNumber u) | t == u -> flowAnn (,TNumber TI32) $ pure $ Op op a b
      (B.GEt, TNumber t, TNumber u) | t == u -> flowAnn (,TNumber TI32) $ pure $ Op op a b
      (B.LEt, TNumber t, TNumber u) | t == u -> flowAnn (,TNumber TI32) $ pure $ Op op a b
      
      -- Type mismatch error
      (_, TNumber t, TNumber u) | t /= u -> E.throwError $ BinOpTypeMismatch apos bpos op at bt
      _ -> E.throwError $ BinOpInvalidTypes apos bpos op at bt
    
    f (Arr []) = R.ask >>= \pos -> E.throwError $ EmptyArray pos
    f (Arr (a:as)) = do
      pos <- R.ask
      let at = snd . fst . unAnn $ a
      let types = fmap (snd . fst . unAnn) as
      if all (== at) types
        then flowAnn (,TArr at (length as + 1)) $ pure $ Arr (a:as)
        else E.throwError $ ArrayElementTypeMismatch pos (at:types)
    
    f (Var n) = do
      pos <- R.ask
      env <- lift $ lift R.ask
      case M.lookup n env of
        Just t -> flowAnn (,t) $ pure $ Var n
        Nothing -> E.throwError $ UnknownBinding pos n
    
    f (Lam params bindings body) = do
      pos <- R.ask
      -- TODO: implement lambda typechecking
      E.throwError $ UnknownBinding pos (B.Ident "lambda-not-implemented")
    
    f (Select sel idx) = do
      pos <- R.ask
      let selType = snd . fst . unAnn $ sel
      let idxType = snd . fst . unAnn $ idx
      
      case selType of
        TArr elemType _ -> do
          case idxType of
            TNumber TI32 -> flowAnn (,elemType) $ pure $ Select sel idx
            TNumber TI64 -> flowAnn (,elemType) $ pure $ Select sel idx
            _ -> E.throwError $ InvalidIndexType (fst . fst . unAnn $ idx) idxType
        _ -> E.throwError $ NotAnArray (fst . fst . unAnn $ sel) selType
    
    f (Rec param bindings body) = do
      pos <- R.ask
      -- TODO: implement rec typechecking
      E.throwError $ UnknownBinding pos (B.Ident "rec-not-implemented")
    
    f _ = do
      pos <- R.ask
      E.throwError $ UnknownBinding pos (B.Ident "unknown-constructor")
