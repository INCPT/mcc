{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecursiveDo #-}

module OSC.Expr.Interpret where

import qualified Control.Monad.Reader as R
import qualified Control.Monad.State as ST

import Data.Bits ((.&.), (.|.), xor, shiftL, shiftR, rotateL, rotateR)

import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as M

import OSC.Expr.Functors
import OSC.Expr.Base
import qualified OSC.Expr.Comp as C

data Value = VNumber C.Number | VArr [Value] | VAbs ([SimM] -> SimM)

instance Show Value where
  show (VNumber (C.I32 n)) = show n
  show (VNumber (C.F32 n)) = show n
  show (VNumber (C.I64 n)) = show n
  show (VNumber (C.F64 n)) = show n
  show (VArr as) = "[" <> intercalate ", " (fmap show as) <> "]"
  show (VAbs _) = "<function>"

type Mem = Map Int Value

data GenState = GenState
  { nextCell :: Int
  , initialMem :: Mem
  }

newtype SimEnv = SimEnv (M.Map C.Ident SimM)
type SimM = R.ReaderT SimEnv (ST.State Mem) Value

type CircuitM = R.ReaderT (Map C.Ident SimM) (ST.State GenState)

-- Helper function to copy the sign from one float to another
copySign :: (RealFloat a) => a -> a -> a
copySign x y = if signum y < 0 then negate (abs x) else abs x

lookupE :: Ord k => String -> M.Map k v -> k -> v
lookupE e m k = case M.lookup k m of
  Just v -> v
  Nothing -> error e

interpret :: Ann C.Type Expr -> CircuitM SimM
interpret (Ann (_, PConst n)) = pure (pure $ VNumber n)

interpret (Ann (_, POp op a b)) = do
  sima <- interpret a
  simb <- interpret b
  pure $ do
    a <- sima
    b <- simb
    case (op, a, b) of
      -- I32 operations
      (C.Add, VNumber (C.I32 a), VNumber (C.I32 b)) -> pure $ VNumber $ C.I32 (a + b)
      (C.Sub, VNumber (C.I32 a), VNumber (C.I32 b)) -> pure $ VNumber $ C.I32 (a - b)
      (C.Mul, VNumber (C.I32 a), VNumber (C.I32 b)) -> pure $ VNumber $ C.I32 (a * b)
      (C.Div, VNumber (C.I32 a), VNumber (C.I32 b)) -> pure $ VNumber $ C.I32 (a `div` b)
      (C.Mod, VNumber (C.I32 a), VNumber (C.I32 b)) -> pure $ VNumber $ C.I32 (a `mod` b)
      (C.Rem, VNumber (C.I32 a), VNumber (C.I32 b)) -> pure $ VNumber $ C.I32 (a `rem` b)
      (C.And, VNumber (C.I32 a), VNumber (C.I32 b)) -> pure $ VNumber $ C.I32 (a .&. b)
      (C.Or, VNumber (C.I32 a), VNumber (C.I32 b)) -> pure $ VNumber $ C.I32 (a .|. b)
      (C.Xor, VNumber (C.I32 a), VNumber (C.I32 b)) -> pure $ VNumber $ C.I32 (a `xor` b)
      (C.Shl, VNumber (C.I32 a), VNumber (C.I32 b)) -> pure $ VNumber $ C.I32 (a `shiftL` fromIntegral b)
      (C.Shr, VNumber (C.I32 a), VNumber (C.I32 b)) -> pure $ VNumber $ C.I32 (a `shiftR` fromIntegral b)
      (C.Rotl, VNumber (C.I32 a), VNumber (C.I32 b)) -> pure $ VNumber $ C.I32 (a `rotateL` fromIntegral b)
      (C.Rotr, VNumber (C.I32 a), VNumber (C.I32 b)) -> pure $ VNumber $ C.I32 (a `rotateR` fromIntegral b)
      (C.Eq, VNumber (C.I32 a), VNumber (C.I32 b)) -> pure $ VNumber $ C.I32 (if a == b then 1 else 0)
      (C.Ne, VNumber (C.I32 a), VNumber (C.I32 b)) -> pure $ VNumber $ C.I32 (if a /= b then 1 else 0)
      (C.Gt, VNumber (C.I32 a), VNumber (C.I32 b)) -> pure $ VNumber $ C.I32 (if a > b then 1 else 0)
      (C.Lt, VNumber (C.I32 a), VNumber (C.I32 b)) -> pure $ VNumber $ C.I32 (if a < b then 1 else 0)
      (C.GEt, VNumber (C.I32 a), VNumber (C.I32 b)) -> pure $ VNumber $ C.I32 (if a >= b then 1 else 0)
      (C.LEt, VNumber (C.I32 a), VNumber (C.I32 b)) -> pure $ VNumber $ C.I32 (if a <= b then 1 else 0)
      (C.Min, VNumber (C.I32 a), VNumber (C.I32 b)) -> pure $ VNumber $ C.I32 (min a b)
      (C.Max, VNumber (C.I32 a), VNumber (C.I32 b)) -> pure $ VNumber $ C.I32 (max a b)

      -- I64 operations
      (C.Add, VNumber (C.I64 a), VNumber (C.I64 b)) -> pure $ VNumber $ C.I64 (a + b)
      (C.Sub, VNumber (C.I64 a), VNumber (C.I64 b)) -> pure $ VNumber $ C.I64 (a - b)
      (C.Mul, VNumber (C.I64 a), VNumber (C.I64 b)) -> pure $ VNumber $ C.I64 (a * b)
      (C.Div, VNumber (C.I64 a), VNumber (C.I64 b)) -> pure $ VNumber $ C.I64 (a `div` b)
      (C.Mod, VNumber (C.I64 a), VNumber (C.I64 b)) -> pure $ VNumber $ C.I64 (a `mod` b)
      (C.Rem, VNumber (C.I64 a), VNumber (C.I64 b)) -> pure $ VNumber $ C.I64 (a `rem` b)
      (C.And, VNumber (C.I64 a), VNumber (C.I64 b)) -> pure $ VNumber $ C.I64 (a .&. b)
      (C.Or, VNumber (C.I64 a), VNumber (C.I64 b)) -> pure $ VNumber $ C.I64 (a .|. b)
      (C.Xor, VNumber (C.I64 a), VNumber (C.I64 b)) -> pure $ VNumber $ C.I64 (a `xor` b)
      (C.Shl, VNumber (C.I64 a), VNumber (C.I64 b)) -> pure $ VNumber $ C.I64 (a `shiftL` fromIntegral b)
      (C.Shr, VNumber (C.I64 a), VNumber (C.I64 b)) -> pure $ VNumber $ C.I64 (a `shiftR` fromIntegral b)
      (C.Rotl, VNumber (C.I64 a), VNumber (C.I64 b)) -> pure $ VNumber $ C.I64 (a `rotateL` fromIntegral b)
      (C.Rotr, VNumber (C.I64 a), VNumber (C.I64 b)) -> pure $ VNumber $ C.I64 (a `rotateR` fromIntegral b)
      (C.Eq, VNumber (C.I64 a), VNumber (C.I64 b)) -> pure $ VNumber $ C.I32 (if a == b then 1 else 0)
      (C.Ne, VNumber (C.I64 a), VNumber (C.I64 b)) -> pure $ VNumber $ C.I32 (if a /= b then 1 else 0)
      (C.Gt, VNumber (C.I64 a), VNumber (C.I64 b)) -> pure $ VNumber $ C.I32 (if a > b then 1 else 0)
      (C.Lt, VNumber (C.I64 a), VNumber (C.I64 b)) -> pure $ VNumber $ C.I32 (if a < b then 1 else 0)
      (C.GEt, VNumber (C.I64 a), VNumber (C.I64 b)) -> pure $ VNumber $ C.I32 (if a >= b then 1 else 0)
      (C.LEt, VNumber (C.I64 a), VNumber (C.I64 b)) -> pure $ VNumber $ C.I32 (if a <= b then 1 else 0)
      (C.Min, VNumber (C.I64 a), VNumber (C.I64 b)) -> pure $ VNumber $ C.I64 (min a b)
      (C.Max, VNumber (C.I64 a), VNumber (C.I64 b)) -> pure $ VNumber $ C.I64 (max a b)

      -- F32 operations
      (C.Add, VNumber (C.F32 a), VNumber (C.F32 b)) -> pure $ VNumber $ C.F32 (a + b)
      (C.Sub, VNumber (C.F32 a), VNumber (C.F32 b)) -> pure $ VNumber $ C.F32 (a - b)
      (C.Mul, VNumber (C.F32 a), VNumber (C.F32 b)) -> pure $ VNumber $ C.F32 (a * b)
      (C.Div, VNumber (C.F32 a), VNumber (C.F32 b)) -> pure $ VNumber $ C.F32 (a / b)
      (C.Eq, VNumber (C.F32 a), VNumber (C.F32 b)) -> pure $ VNumber $ C.I32 (if a == b then 1 else 0)
      (C.Ne, VNumber (C.F32 a), VNumber (C.F32 b)) -> pure $ VNumber $ C.I32 (if a /= b then 1 else 0)
      (C.Gt, VNumber (C.F32 a), VNumber (C.F32 b)) -> pure $ VNumber $ C.I32 (if a > b then 1 else 0)
      (C.Lt, VNumber (C.F32 a), VNumber (C.F32 b)) -> pure $ VNumber $ C.I32 (if a < b then 1 else 0)
      (C.GEt, VNumber (C.F32 a), VNumber (C.F32 b)) -> pure $ VNumber $ C.I32 (if a >= b then 1 else 0)
      (C.LEt, VNumber (C.F32 a), VNumber (C.F32 b)) -> pure $ VNumber $ C.I32 (if a <= b then 1 else 0)
      (C.Min, VNumber (C.F32 a), VNumber (C.F32 b)) -> pure $ VNumber $ C.F32 (min a b)
      (C.Max, VNumber (C.F32 a), VNumber (C.F32 b)) -> pure $ VNumber $ C.F32 (max a b)
      (C.CopySign, VNumber (C.F32 a), VNumber (C.F32 b)) -> pure $ VNumber $ C.F32 (copySign a b)
      (C.Rem, VNumber (C.F32 a), VNumber (C.F32 b)) -> pure $ VNumber $ C.F32 (snd (properFraction (a / b)) * b)

      -- F64 operations
      (C.Add, VNumber (C.F64 a), VNumber (C.F64 b)) -> pure $ VNumber $ C.F64 (a + b)
      (C.Sub, VNumber (C.F64 a), VNumber (C.F64 b)) -> pure $ VNumber $ C.F64 (a - b)
      (C.Mul, VNumber (C.F64 a), VNumber (C.F64 b)) -> pure $ VNumber $ C.F64 (a * b)
      (C.Div, VNumber (C.F64 a), VNumber (C.F64 b)) -> pure $ VNumber $ C.F64 (a / b)
      (C.Eq, VNumber (C.F64 a), VNumber (C.F64 b)) -> pure $ VNumber $ C.I32 (if a == b then 1 else 0)
      (C.Ne, VNumber (C.F64 a), VNumber (C.F64 b)) -> pure $ VNumber $ C.I32 (if a /= b then 1 else 0)
      (C.Gt, VNumber (C.F64 a), VNumber (C.F64 b)) -> pure $ VNumber $ C.I32 (if a > b then 1 else 0)
      (C.Lt, VNumber (C.F64 a), VNumber (C.F64 b)) -> pure $ VNumber $ C.I32 (if a < b then 1 else 0)
      (C.GEt, VNumber (C.F64 a), VNumber (C.F64 b)) -> pure $ VNumber $ C.I32 (if a >= b then 1 else 0)
      (C.LEt, VNumber (C.F64 a), VNumber (C.F64 b)) -> pure $ VNumber $ C.I32 (if a <= b then 1 else 0)
      (C.Min, VNumber (C.F64 a), VNumber (C.F64 b)) -> pure $ VNumber $ C.F64 (min a b)
      (C.Max, VNumber (C.F64 a), VNumber (C.F64 b)) -> pure $ VNumber $ C.F64 (max a b)
      (C.CopySign, VNumber (C.F64 a), VNumber (C.F64 b)) -> pure $ VNumber $ C.F64 (copySign a b)
      (C.Rem, VNumber (C.F64 a), VNumber (C.F64 b)) -> pure $ VNumber $ C.F64 (snd (properFraction (a / b)) * b)

      _ -> error $ "interpret Op: unsupported operation: " ++ show (op, a, b)

interpret (Ann (_, PArr as)) = do
  simas <- traverse interpret as
  pure $ do
    as <- sequence simas
    pure $ VArr as

interpret (Ann (_, PIVar n)) = do
  env <- R.ask
  case M.lookup n env of
    Just var -> pure var
    Nothing -> error $ "interpret: var not in scope: " <> show n

interpret (Ann (_, PLam _ params bindings body)) = mdo
  simbindings <- fmap M.fromList $ sequence $ mconcat
    [ [ (p,) <$> pure (R.ask >>= \(SimEnv env) -> lookupE (show p) env p) | p <- params ]
    , [ fmap (n,) $ R.local (\env -> simbindings <> env) $ interpret bbody
      | (n, bbody) <- bindings
      ]
    ]
  simbody <- R.local (\env -> simbindings <> env) $ interpret body

  pure $ do
    SimEnv env <- R.ask
    pure $ VAbs $ \args -> R.local (\(SimEnv env') -> SimEnv (M.fromList (zip params args) <> env' <> env)) simbody

interpret (Ann (_, PApp f params)) = do
  simargs <- traverse interpret params
  simf <- interpret f
  pure $ do
    f <- simf
    case f of
      VAbs f -> f simargs
      _ -> error "App: f not a function"

interpret (Ann (_, PSelect expr idx)) = do
  simexpr <- interpret expr
  simidx <- interpret idx
  pure $ do
    e <- simexpr
    i <- simidx
    case (e, i) of
      (VArr as, VNumber (C.I32 i')) -> pure (as !! i')
      (VArr as, VNumber (C.I64 i')) -> pure (as !! i')
      (e', i') -> error $ "Select: " <> show e' <> ", " <> show i'

interpret (Ann (t, PRec _ delay param bindings body)) = mdo
  nextCell <- ST.gets (.nextCell)

  let delayBufferIdx = nextCell
  let delayIndexIdx = nextCell + 1

  let initialValue = alloc (C.TArr t delay)

  ST.modify $ \st -> st
    { nextCell = st.nextCell + 2
    , initialMem = M.fromList [(delayBufferIdx, initialValue), (delayIndexIdx, VNumber (C.I32 0))] <> st.initialMem
    }

  let delayLine = ST.get >>= \mem -> do
        let delayBuffer = lookupE "delayBuffer" mem delayBufferIdx
        let delayIdx = lookupE "delayIdx" mem delayIndexIdx
        case (delayBuffer, delayIdx) of
          (VArr ds, VNumber (C.I32 i)) -> pure (ds !! i)
          _ -> error $ "delayLine: (this is a bug): " <> show delayBuffer <> ", " <> show delayIdx

  simbindings <- fmap M.fromList $ sequence $ mconcat
    [ [ pure (param, delayLine) ]
    , [ fmap (n,) $ R.local (\env -> simbindings <> env) $ interpret bbody | (n, bbody) <- bindings ]
    ]

  simbody <- R.local (\env -> simbindings <> env) $ interpret body

  pure $ do
    env <- R.ask
    mem <- ST.get

    let (nextValue, mem') = ST.runState (R.runReaderT simbody env) mem

    let delayBuffer = lookupE "delayBuffer: tick" mem' delayBufferIdx
    let delayIndex = lookupE "delayIndex: tick" mem' delayIndexIdx

    d <- delayLine

    ST.put $ mconcat
      -- Update delay lines
      [ case (delayBuffer, delayIndex) of
          (VArr ds, VNumber (C.I32 i)) -> M.fromList
            [ (delayBufferIdx, VArr $ replace i nextValue ds)
            , (delayIndexIdx, VNumber (C.I32 ((i + 1) `mod` delay)))
            ]
          _ -> error "delayLine2 (this is a bug)"

      , mem'
      ]

    pure d
  where
    replace i a as = take i as <> [a] <> drop (i + 1) as

    alloc (C.TNumber C.TI32) = VNumber (C.I32 0)
    alloc (C.TNumber C.TF32) = VNumber (C.F32 0)
    alloc (C.TNumber C.TI64) = VNumber (C.I64 0)
    alloc (C.TNumber C.TF64) = VNumber (C.F64 0)
    alloc (C.TArr t n) = VArr $ take (n + 1) $ repeat (alloc t)
    alloc (C.TLam _ _) = error "interpret: Rec: function in return type"

interpretToList :: Int -> Ann C.Type Expr -> [Value]
interpretToList n texpr = take n (go st.initialMem sim)
  where
    go mem sim = let (a, mem') = ST.runState (R.runReaderT sim (SimEnv mempty)) mem in a:go mem' sim
    (sim, st) = ST.runState (R.runReaderT (interpret texpr) mempty) (GenState { nextCell = 0, initialMem = mempty })
