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

import Data.Functor.Identity (Identity)
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

newtype FuncRef = FuncRef Int deriving (Eq, Ord, Show)
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

data Op

data IR m
  = Alloc Type Bool (Ref -> m (IR m))
  | Arg Int Type (Ref -> m (IR m))

  | CopyVal Number Ref Lens (IR m)
  | CopyRef Ref Ref Lens (IR m)

  | BinOp Op Ref Ref Ref (IR m)
  | Call Ref [Ref] Ref (IR m)

  | Done

data Mut = Mut
  { funcRefs :: Map FuncRef (IR Identity)
  , nextFuncRefIdx :: Int
  }

data Expr

fr :: IR (ST.StateT Mut (R.Reader Env)) -> IR (ST.StateT Mut (R.Reader Env))
fr = undefined

lower :: IR (ST.StateT Mut (R.Reader Env)) -> IR Identity
lower = undefined

-- bla :: Expr -> ST.StateT Mut (R.Reader Env) IR
-- bla = undefined
-- 
-- lol :: ST.StateT Mut (R.Reader Env) IR -> ST.StateT Mut (R.Reader Env) IR
-- lol m = do
--   idx <- ST.gets (.nextFuncRefIdx); ST.modify $ \st -> st { nextFuncRefIdx = st.nextFuncRefIdx + 1 }
-- 
--   ir <- m
-- 
--   ST.modify $ \st -> st { funcRefs = M.insert (FuncRef idx) ir st.funcRefs }
--   pure ir

newtype CallM m a = CallM { callM :: R.ReaderT Env (ST.StateT Mut m) a }
  deriving (Functor, Applicative, Monad) -- , MonadTrans, MFunctor)

-- this doesn't need to be here
withBindings :: MonadFix m => [(Ident, CallM m Ref)] -> CallM m () -> CallM m ()
withBindings bs f = CallM $ mdo
  bsRefs <- fmap M.fromList $ sequence
    [ do
        r <- R.local (\env -> env { refs = bsRefs <> env.refs }) b.callM
        pure (i, r)
    | (i, b) <- bs
    ]

  R.local (\env -> env { refs = bsRefs <> env.refs }) f.callM

-- this doesn't need to be here
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

-- TODO: we need Map FuncRef [m ()] and a memory layout 

funcRef :: Type -> ([Ref] -> CallM m Ref) -> CallM m Ref
funcRef t f = CallM $ do
  -- let a = R.runReaderT (ST.runStateT (f []).callM undefined) undefined
  -- let a = ST.runStateT (R.runReaderT (f []).callM undefined)
  -- args <- lift $ sequence [ arg i p | (i, p) <- zip [0..] (paramTypes t) ]
  
  -- TODO: call retVal
  undefined

-- TODO: here we must know the captured values
-- in graph code if a function returns a function we can just fold everything inside the returned function (everything is immutable)
-- in sync code we'll need to allocate the Ref in a the global area
allocAndCall :: Type -> Bool -> CallM m () -> CallM m Ref
allocAndCall t global (CallM m) = undefined
