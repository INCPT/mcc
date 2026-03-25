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

data Type = TNumber | TArr Type {- length -} Int | TAbs Type Type
  deriving Show

sizeOfType :: Type -> Int
sizeOfType = undefined

paramTypes :: Type -> [Type]
paramTypes (TAbs t r) = t:paramTypes r
paramTypes _ = []

data VType = VTNumber | VTArr Type Int

returnType :: Type -> VType
returnType TNumber = VTNumber
returnType (TArr t dim) = VTArr t dim
returnType (TAbs _ r) = returnType r

data Ident = Ident Int deriving (Eq, Ord, Show)
data Number = I32 Int | I64 Int | F32 Float | F64 Double deriving (Eq, Ord, Show)

newtype FuncRef = FuncRef Int deriving (Eq, Ord, Show)
newtype GlobalIdx = GlobalIdx Int deriving (Eq, Ord, Show)
data Idx = Local Int | Global Int deriving (Eq, Ord, Show)
newtype ArrayBaseAddr = ArrayBaseAddr Idx deriving (Eq, Ord, Show)
newtype ArgPos = ArgPos Int deriving (Eq, Ord, Show)

data Ref 
  = RVar Idx -- either a function local var index (e.g. in function f() { int a; float b; } would be locals with index 0 and 1) or an index into a global var table
  | RArray Type Int ArrayBaseAddr -- global base address of array in a linear memory layout
  | RFuncRef FuncRef -- index into a global function table

  -- double references
  | RRArray Type Idx -- contains the local/global var index containing the base address of an array
  | RRFuncRef Idx -- contains the local/global var index containing the index into the function table
  deriving Show

data Value = VConst Int | VVar Idx | VVVar Idx
  deriving Show

refToValue :: Either Int Ref -> Value
refToValue (Left idx) = VConst idx
refToValue (Right (RVar idx)) = VVar idx
refToValue e = error $ "refToValue: " <> show e <> " (this is a bug)"

--------------------------------------------------------------------------------

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

data Lens = Lens { from :: [Value], to :: [Int] }

focusLensFrom :: Value -> Lens -> Lens
focusLensFrom i l = l { from = i:l.from }

focusLensTo :: Int -> Lens -> Lens
focusLensTo i l = l { to = i:l.to }

data Env = Env {
  typ :: Type,
  ret :: Ref,
  lens :: Lens
}

data Op

data AllocRegion = ARGlobal | ARLocal

data IRF n
  = Ref Ref
  | Arg Int

  | Alloc Type AllocRegion (Ref -> n)

  -- copies a constant into the Ref that must be an RVar or an RArray/RRArray with lens.to focused on a single element
  | CopyConst Type Number Ref Lens n

  -- copies the value referenced by the first Ref into the second Ref respecting both lens.from and lens.to
  -- the N-D (N dimensional) lens describes two N-D subslices of an M-D source tensor to a a K-D destination tensor (N >= 1, M >= N, K >= N)
  | CopyRef Type Ref Ref Lens n

  | BinOp Op Ref Ref Ref n

  | Call Ref [Ref] Ref -- first Ref must be an RFuncRef or an RRFuncRef; then arguments; then destination
  deriving (Functor)

type IR = Free IRF
type IRT = FreeT IRF

alloc :: Type -> AllocRegion -> IR Ref
alloc t b = liftF (Alloc t b id)

arg :: Int -> IR ()
arg i = liftF (Arg i)

call :: Ref -> [Ref] -> Ref -> IR ()
call fr args ret = Free (Call fr args ret)

-- copyVal :: Number -> Ref -> Lens -> IR m ()
-- copyVal n r l = liftF (CopyVal n r l ())
-- 
-- copyRef :: Ref -> Ref -> Lens -> IR m ()
-- copyRef r1 r2 l = liftF (CopyRef r1 r2 l ())
-- 
-- binOp :: Op -> Ref -> Ref -> Ref -> IR m ()
-- binOp op r1 r2 r3 = liftF (BinOp op r1 r2 r3 ())
-- 
-- call :: Ref -> [Ref] -> Ref -> IR m ()
-- call r rs r' = liftF (Call r rs r' ())

data Mut = Mut {
  funcRefs :: Map FuncRef (IR ()),
  nextFuncRefIdx :: Int,
  nextAlloc :: Int
}

data Expr

-- TODO: interpret allocates given an allocation strategy (Type Bool -> ST.State st Ref)

{-
interpret :: IR () -> ST.State Mut (IR ())
interpret (Pure a) = pure $ Pure a
interpret (Free (Abs t body)) = do
  idx <- ST.gets (.nextFuncRefIdx); ST.modify $ \st -> st { nextFuncRefIdx = st.nextFuncRefIdx + 1 }
  lbody <- interpret body
  ST.modify $ \st -> st { funcRefs = M.insert (FuncRef idx) lbody st.funcRefs }
  pure $ liftF $ Ref $ RFuncRef $ FuncRef idx
interpret (Free (Alloc t g next)) = do
  idx <- ST.gets (.nextAlloc); ST.modify $ \st -> st { nextAlloc = st.nextAlloc + 1 }
  interpret (next $ RVar $ Local $ idx)
interpret (Free (Ref r)) = pure $ liftF $ Ref r
interpret (Free (Arg i)) = pure $ liftF $ Arg i
interpret (Free (CopyVal t n r l next)) = do
  rest <- interpret next
  pure $ Free $ CopyVal t n r l rest
interpret (Free (CopyRef t r1 r2 l next)) = do
  rest <- interpret next
  pure $ Free $ CopyRef t r1 r2 l rest
interpret (Free (BinOp op r1 r2 r3 next)) = do
  rest <- interpret next
  pure $ Free $ BinOp op r1 r2 r3 rest
interpret (Free (Call r rs r')) = pure $ Free $ Call r rs r'

lower :: Env -> IRT (R.Reader Env) a -> IR a
lower env m = case R.runReader (TF.runFreeT m) env of
  TF.Pure a -> Pure a
  TF.Free ir -> case ir of
    Ref r -> Free $ Ref r
    Arg i -> Free $ Arg i
    Alloc t g next -> Free $ Alloc t g (\r -> lower env (next r))
    CopyVal t n r l next -> Free $ CopyVal t n r l (lower env next)
    CopyRef t r1 r2 l next -> Free $ CopyRef t r1 r2 l (lower env next)
    BinOp op r1 r2 r3 next -> Free $ BinOp op r1 r2 r3 (lower env next)
    Call r rs r' -> Free $ Call r rs r'
    Abs t body -> Free $ Abs t (lower env body)

--------------------------------------------------------------------------------

retVal :: Number -> IRT (R.Reader Env) ()
retVal n = FreeT $ do
  env <- R.ask
  pure $ TF.Free $ CopyVal env.typ n env.ret env.lens (pure ())

retRef :: Ref -> IRT (R.Reader Env) ()
retRef ref = FreeT $ do
  env <- R.ask
  pure $ TF.Free $ CopyRef env.typ ref env.ret env.lens (pure ())

-- API -------------------------------------------------------------------------

select :: IRT (R.Reader Env) a -> Either Int Ref -> IRT (R.Reader Env) a
select ir ref = TF.hoistFreeT (R.local $ \env -> env { lens = focusLensFrom (refToValue ref) env.lens }) ir

focus :: Int -> IRT (R.Reader Env) a -> IRT (R.Reader Env) a
focus i = TF.hoistFreeT $ R.local $ \env -> env { lens = focusLensTo i env.lens }

choice :: [IRT (R.Reader Env) ()] -> Ref -> IRT (R.Reader Env) ()
choice = undefined

allocAndCall :: Type -> AllocRegion -> IRT (R.Reader Env) () -> IRT (R.Reader Env) Ref
allocAndCall t region ir = TF.FreeT $ pure $ TF.Free $ Alloc t region $ \ref -> TF.FreeT $ R.local (const $ env ref) $ TF.runFreeT (ir >> pure ref)
  where
    env ref = Env {
      typ = t,
      ret = ref,
      lens = Lens { from = [], to = [] }
    }

funcRef :: IRT (R.Reader Env) (Either Number Ref) -> IRT (R.Reader Env) ()
funcRef ir = TF.FreeT $ TF.runFreeT (ir >>= either retVal retRef)

--------------------------------------------------------------------------------

newtype CallM m a = CallM { callM :: R.ReaderT Env (ST.StateT Mut m) a }
  deriving (Functor, Applicative, Monad) -- , MonadTrans, MFunctor)

-- this doesn't need to be here
-- withBindings :: MonadFix m => [(Ident, CallM m Ref)] -> CallM m () -> CallM m ()
-- withBindings bs f = CallM $ mdo
--   bsRefs <- fmap M.fromList $ sequence
--     [ do
--         r <- R.local (\env -> env { refs = bsRefs <> env.refs }) b.callM
--         pure (i, r)
--     | (i, b) <- bs
--     ]
-- 
--   R.local (\env -> env { refs = bsRefs <> env.refs }) f.callM
-- 
-- -- this doesn't need to be here
-- capture :: Monad m => Ident -> CallM m Ref
-- capture n = CallM $ R.asks (M.lookup n . (.refs)) >>= \case
--   Just ref -> pure ref
--   Nothing -> error "capture: no binding (this is a bug)"
-- 
-- external :: Ident -> [Ref] -> CallM m ()
-- external = undefined
-}