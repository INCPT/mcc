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

import Data.Functor.Identity (Identity (Identity))
import Control.Monad (when)
import Control.Monad.Fix (MonadFix)
import Control.Monad.Trans (MonadTrans, lift)
import qualified Control.Monad.Reader as R
import qualified Control.Monad.State as ST
import Data.Functor.Product (Product (Pair))
import Data.Map (Map)
import qualified Data.Map as M
import Control.Monad.Free (Free (Free, Pure), liftF)
import qualified Control.Monad.Trans.Free as TF
import Control.Monad.Trans.Free (FreeT (FreeT), FreeF)
import OSC.Ctx

data Idx = Local Int | Global Int deriving (Eq, Ord, Show)
newtype ArrayBaseAddr = ArrayBaseAddr Idx deriving (Eq, Ord, Show)
newtype ArgPos = ArgPos Int deriving (Eq, Ord, Show)

data Ref 
  = RArg Int

  | RVar Idx -- either a function local var index (e.g. in function f() { int a; float b; } would be locals with index 0 and 1) or an index into a global var table
  | RArray Type Int ArrayBaseAddr -- global base address of array in a linear memory layout
  | RFuncRef FuncRef -- index into a global function table

  -- double references
  | RRArray Type Idx -- contains the local/global var index containing the base address of an array
  | RRFuncRef Idx -- contains the local/global var index containing the index into the function table
  deriving Show

--------------------------------------------------------------------------------

-- INFORMAL SPECS

-- the calling convention is: simple values and references on the stack + a reference to where the result must be placed; the caller allocates the destination

-- for example when the function(x: i32, y: i32): i32[2][2] { return [[x, y], f(x + y)] } is called:
--   the caller allocates a flat i32 array with 2 * 2 elements
--   puts x and y on stack, calls function
--   when an array is returned we traverse each element and add its index into lens.to
--     the nested array traverses in turn ints elements and adds each one to lens.to
--       for example when coming to 'y' we'd be in the first element of the outer array and the second element of the inner (i.e. lens.to = [0, 1])
--       since 'y' is a value and can't be evaluated further we copy it using CopyConst or CopyRef to the destination slice (lens.to)
--     when calling f(x + y) its return value reference is computed as current_ret_reference + offset of element [0][1] into flat return array
--       this means essentially zero copying of data
--  on the other hand if we return a selection (e.g. f()[x][y]) (so f() is higher dimensional than the return type of the current function)
--    then space for the return value ret_val of f() is allocated, f called and a CopyRef operation (reference to ret_val, lens.from = [x][y]) => (current_ret_reference, lens.to = [...]) performed

-- NOTE: a literal array paired with a selection is a choice

newtype Lens = Lens { to :: [Int] }

data Env = Env {
  typ :: Type,
  ret :: Ref,
  lens :: Lens
}

newEnv :: Type -> Ref -> Env
newEnv t ref = Env t ref (Lens [])

focusLens :: Int -> Lens -> Lens
focusLens i l = l { to = i:l.to }

focusEnv :: Int -> Env -> Env
focusEnv i env = env { lens = focusLens i env.lens }

data IRF n
  = Ref Ref

  | Alloc Type AllocRegion (Ref -> n)

  -- copies a constant into the Ref that must be an RVar or an RArray/RRArray with lens.to focused on a single element
  | CopyConst Type Number Ref Lens

  -- copies the value referenced by the first Ref into the second Ref respecting both lens.from and lens.to
  -- the N-D (N dimensional) lens describes two N-D subslices of an M-D source tensor to a a K-D destination tensor (N >= 1, M >= N, K >= N)
  | CopyRef Type Ref Ref Lens

  | BinOp Op Ref Ref Ref

  | Call Ref [Ref] Ref -- first Ref must be an RFuncRef or an RRFuncRef; then arguments; then destination
  deriving Functor

type IR = Free IRF

copyConst :: Type -> Number -> Ref -> Lens -> IR ()
copyConst t n ref lens = liftF $ CopyConst t n ref lens

copyRef :: Type -> Ref -> Ref -> Lens -> IR ()
copyRef t src dst lens = liftF $ CopyRef t src dst lens

binOp :: Op -> Ref -> Ref -> Ref -> IR ()
binOp op r1 r2 r3 = liftF $ BinOp op r1 r2 r3

call :: Ref -> [Ref] -> Ref -> IR ()
call funcRef args dst = liftF $ Call funcRef args dst

alloc :: Type -> AllocRegion -> IR Ref
alloc t region = liftF $ Alloc t region id

ref :: Ref -> IR Ref
ref r = pure r

--------------------------------------------------------------------------------

choiceToIR :: Map Ident Type -> Choice -> R.ReaderT Env IR ()
choiceToIR _ (CExpr _ (SConst n)) = do
  env <- R.ask
  lift $ copyConst (numberType n) n env.ret env.lens
choiceToIR _ (CExpr _ (SFuncRef t fr)) = do
  env <- R.ask
  lift $ copyConst t (funcRefConst fr) env.ret env.lens
choiceToIR globals (CExpr [] (SArr _ elems)) = sequence_
  [ R.local (focusEnv i) $ choiceToIR globals elem
  | (i, elem) <- zip [0..] elems
  ]
choiceToIR _ (CExpr _ (SArr _ _)) = error "choiceToIR: SArr: non empty selection indices (this is a bug)"
choiceToIR globals (CExpr _ (SOp _ op a b)) = do
  env <- R.ask

  aref <- lift $ alloc (choiceType a) ALocal
  bref <- lift $ alloc (choiceType b) ALocal

  R.local (const $ newEnv (choiceType a) aref) (choiceToIR globals a)
  R.local (const $ newEnv (choiceType b) bref) (choiceToIR globals b)
  
  lift $ binOp op aref bref env.ret

choiceToIR _ (CExpr _ (SAbs _ _ _)) = error "choiceToIR: SAbs: (this is a bug)"
choiceToIR _ _ = undefined
