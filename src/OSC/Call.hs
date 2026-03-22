{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}

module OSC.Call where

import Data.Functor.Identity
import Control.Monad (when)
import Control.Monad.Trans (MonadTrans, lift)
import qualified Control.Monad.Reader as R
import qualified Control.Monad.State as ST
import Data.Functor.Product (Product (Pair))
import Data.Map (Map)
import qualified Data.Map as M

data Type = TNumber | TArr Type {- length -} Int | TAbs Type Type
  deriving Show

paramTypes :: Type -> [Type]
paramTypes (TAbs t r) = t:paramTypes r
paramTypes _ = []

data VType = VTNumber | VTArr Type Int

returnType :: Type -> VType
returnType TNumber = VTNumber
returnType (TArr t dim) = VTArr t dim
returnType (TAbs _ r) = returnType r

data Slice = Slice { start :: Int, length :: Int, innerDims :: [Int] }

data State m = State
  { nextArrayIdx :: Int
  , nextFuncRef :: Int
  , funcRefs :: Map Int (FuncRef m)
  }

data Env = Env
  { slice :: Slice
  }

newtype CallM m a = CallM { run :: R.ReaderT Env (ST.StateT (State m) m) a }
  deriving (Functor, Applicative, Monad)

data Ident
data Number = I32 Int | F32 Float

data Value = VConst Number | VArr [Value]

data FuncRef m = FuncRef Int Type (M.Map Ident (Ref m)) ([Ref m] -> m Value)
data Ref m = RConst Number | RLocal Int | RArray Slice Int | RFuncRef (FuncRef m)

binOp :: Ref m -> Ref m -> CallM m (Ref m)
binOp = undefined

-- if not in a return context, alloc one
func :: Monad m => Type -> M.Map Ident (CallM m (Ref m)) -> ([Ref m] -> CallM m Value) -> CallM m (FuncRef m)
func t bindings f = CallM $ do
  nfr <- ST.gets (.nextFuncRef); ST.modify $ \st -> st { nextFuncRef = st.nextFuncRef + 1 }

  -- let a = R.runReaderT (ST.runStateT ((f undefined).run) undefined) undefined
  --- let a = ST.runStateT (R.runReaderT ((f undefined).run) undefined) undefined

  let fr = FuncRef nfr t undefined undefined

  ST.modify $ \st -> st { funcRefs = M.insert nfr fr st.funcRefs }
  pure fr

call :: Monad m => FuncRef m -> [Ref m] -> CallM m (Ref m)
call (FuncRef _ t bindings f) args = case drop (length args) (paramTypes t) of
    [] -> undefined
    _ -> undefined