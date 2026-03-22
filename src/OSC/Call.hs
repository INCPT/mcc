{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}

module OSC.Call where

import Data.Functor.Identity
import Control.Monad (when)
import Control.Monad.Trans (MonadTrans, lift)
import qualified Control.Monad.Reader as R
import qualified Control.Monad.State as ST
import qualified Data.Map as M

data Type = TNumber | TArr Type {- length -} Int | TAbs Type Type
  deriving Show

data Slice = Slice { start :: Int, length :: Int, innerDims :: [Int] }

data State m = State
  { nextArrayIdx :: Int
  , nextFuncRef :: Int
  , funcRefs :: M.Map Int ([Ref] -> m Ref)
  }

data Env = Env
  { slice :: Slice
  }

newtype CallM m a = CallM { run :: ST.StateT (State m) (R.ReaderT Env m) a }
  deriving (Functor, Applicative, Monad)

instance MonadTrans CallM where
  lift f = CallM $ lift $ lift f

data Number = I32 Int | F32 Float

data Value = VConst Number | VArr [Value]
data VType = VNumber | VArray VType Int

-- returnType :: Type -> VType
-- returnType TNumber = VNumber
-- returnType (TArr t dim) = VArr (map returnType t) dim

data FuncRef
data Ref

binOp :: Ref -> Ref -> CallM m Ref
binOp = undefined

-- if not in a return context, alloc one
func :: Monad m => Type -> ([Ref] -> CallM m Ref) -> CallM m FuncRef
func t f = CallM $ do
  st <- ST.get
  ST.put $ st { nextArrayIdx = st.nextArrayIdx + 1 }
  a <- (f undefined).run
  undefined

call :: FuncRef -> [Ref] -> Either Ref FuncRef
call = undefined