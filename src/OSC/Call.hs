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
newtype ArrayIdx = ArrayIdx Idx deriving (Eq, Ord, Show)
newtype ArgPos = ArgPos Int deriving (Eq, Ord, Show)

data Ref 
  = RVar Idx
  | RArray Type Int ArrayIdx
  | RFuncRef FuncRef

  -- double references
  | RRVar Idx -- var pointing to var (?)
  | RRArray Type Int Idx -- var containing base address
  | RRFuncRef Idx -- var containing func idx
  deriving Show

data Value = VConst Int | VVar Idx | VVVar Idx
  deriving Show

refToValue :: Either Int Ref -> Value
refToValue (Left idx) = VConst idx
refToValue (Right (RVar idx)) = VVar idx
refToValue (Right (RRVar idx)) = VVVar idx
refToValue e = error $ "refToValue: " <> show e <> " (this is a bug)"

--------------------------------------------------------------------------------

data Lens = Lens { from :: [Value], to :: [Int] }

focusLensFrom :: Value -> Lens -> Lens
focusLensFrom i l = l { from = i:l.from }

focusLensTo :: Int -> Lens -> Lens
focusLensTo i l = l { to = i:l.to }

data Env = Env {
  typ :: Type,
  ret :: Ref,
  refs :: Map Ident Ref,
  lens :: Lens
}

data Op

data AllocRegion = ARGlobal | ARLocal

data IRF n
  = Ref Ref
  | Arg Int

  | Alloc Type AllocRegion (Ref -> n)

  | CopyVal Type Number Ref Lens n
  | CopyRef Type Ref Ref Lens n

  | BinOp Op Ref Ref Ref n
  | Call Ref [Ref] Ref

  | Abs Type n
  deriving (Functor)

type IR = Free IRF
type IRT = FreeT IRF

data IIRF n
  = IFuncRef FuncRef
  | IAlloc Type Bool (Ref -> n)
  | IArg Int Type (Ref -> n)

  | ICopyVal Number Ref Lens n
  | ICopyRef Ref Ref Lens n

  | IBinOp Op n n Ref n
  | ICall n [n] Ref n
  deriving (Functor)

-- Smart constructors
alloc :: Type -> AllocRegion -> IR Ref
alloc t b = liftF (Alloc t b id)

arg :: Int -> IR ()
arg i = liftF (Arg i)

abs :: Type -> IR () -> IR ()
abs t n = Free (Abs t n)

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

allocAndCall :: Type -> AllocRegion -> IRT (R.Reader Env) () -> IRT (R.Reader Env) Ref
allocAndCall t region ir = TF.FreeT $ pure $ TF.Free $ Alloc t region $ \ref -> TF.FreeT $ R.local (fenv ref) $ TF.runFreeT (ir >> pure ref)
  where
    fenv ref env = env {
      typ = t,
      ret = ref,
      lens = Lens { from = [], to = [] }
    }

funcRef :: IRT (R.Reader Env) Ref -> IRT (R.Reader Env) ()
funcRef ir = TF.FreeT $ TF.runFreeT (ir >>= retRef)

--------------------------------------------------------------------------------

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

external :: Ident -> [Ref] -> CallM m ()
external = undefined