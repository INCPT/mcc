{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TupleSections #-}

module OSC.Call where

import Data.Functor.Identity
import Control.Monad (when)
import Control.Monad.Fix (MonadFix)
import Control.Monad.Trans (MonadTrans, lift)
import qualified Control.Monad.Reader as R
import qualified Control.Monad.State as ST
import Data.Functor.Product (Product (Pair))
import Data.Map (Map)
import qualified Data.Map as M
import Control.Monad.Morph (MFunctor, hoist)

data Type = TNumber | TArr Type {- length -} Int | TAbs Type Type

paramTypes :: Type -> [Type]
paramTypes (TAbs t r) = t:paramTypes r
paramTypes _ = []

data VType = VTNumber | VTArr Type Int

returnType :: Type -> VType
returnType TNumber = VTNumber
returnType (TArr t dim) = VTArr t dim
returnType (TAbs _ r) = returnType r

data Ident = Ident Int deriving (Eq, Ord, Show)
data Number

newtype FuncRef = FuncRef Int
newtype GlobalIdx = GlobalIdx Int
data Idx = Local Int | Global Int
newtype ArrayIdx = ArrayIdx Idx
newtype ArgPos = ArgPos Int

data Ref 
  = RVar Idx
  | RArray Type Int ArrayIdx
  | RFuncRef FuncRef

  -- double references
  | RRLocal Idx -- var pointing to var (?)
  | RRArray Type Int Idx -- var containing base address
  | RRFuncRef Idx -- var containing func idx

--------------------------------------------------------------------------------

data Value = VConst Number | VRef Idx | VVRef Idx

data Lens = Lens { typ :: Type, from :: Value, to :: Int, count :: Int }

data Env = Env
  { typ :: Type
  , ret :: Ref
  , refs :: Map Ident Ref
  , focus :: Lens
  }

-- data State = State
--   { captured :: Set Ref
--   }

class MonadCodegen m where
  arg :: Int -> Type -> m Ref

  copyVal :: Number -> Ref -> Lens -> m ()
  copyRef :: Ref -> Ref -> Lens -> m ()

  call :: Ref -> [Ref] -> Ref -> m ()

newtype CallM m a = CallM { callM :: ST.StateT () (R.ReaderT Env m) a }
  deriving (Functor, Applicative, Monad)

withBindings :: MonadFix m => [(Ident, CallM m Ref)] -> CallM m () -> CallM m ()
withBindings bs f = CallM $ mdo
  bsRefs <- fmap M.fromList $ sequence
    [ do
        r <- R.local (\env -> env { refs = bsRefs <> env.refs }) b.callM
        pure (i, r)
    | (i, b) <- bs
    ]

  R.local (\env -> env { refs = bsRefs <> env.refs }) f.callM

-- if capturing argument need to declare it globally; otherwise just declare Ref global
capture :: Monad m => Ident -> CallM m Ref
capture n = CallM $ R.asks (M.lookup n . (.refs)) >>= \case
  Just ref -> pure ref
  Nothing -> error "capture: no binding (this is a bug)"

focus :: Int -> CallM m () -> CallM m ()
focus = undefined

select :: CallM m () -> Ref -> CallM m ()
select = undefined

external :: Ident -> [Ref] -> CallM m ()
external = undefined

-- we need Map FuncRef [m ()] and a memory layout 

funcRef :: Type -> ([Ref] -> CallM m Ref) -> CallM m Ref
funcRef t f = CallM $ do
  -- args <- lift $ sequence [ arg i p | (i, p) <- zip [0..] (paramTypes t) ]
  
  -- TODO: call retVal
  undefined

-- call :: Ref -> [Ref] -> CallM m ()
-- call = undefined

-- TODO: here we must know the captured values
allocAndCall :: MonadCodegen m => Type -> CallM m () -> CallM m Ref
allocAndCall t (CallM m) = undefined
