{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecursiveDo #-}

module OSC.Box where

import qualified Control.Monad.State as ST
import Control.Monad.State.Lazy (State)

import qualified Data.Map as M
import Data.Map (Map)

data Number = I Int | F Double
  deriving Show

data Ident = Ident String
  deriving (Eq, Ord, Show)

data Box
  = BConst Number
  | BVar Ident
  | BDelay Ident Int Box
  | BFunc String Box Box -- TODO: func must be pure

flow :: Box -> String
flow (BConst n) = show n
flow (BVar (Ident v)) = v
flow (BFunc f a b) = "((" <> flow a <> ") " <> f <> " (" <> flow b <> "))"
flow (BDelay (Ident n) _ _) = n

gatherDelays :: Box -> [(Ident, Box)]
gatherDelays (BDelay n _ b) = [(n, b)]
gatherDelays (BFunc _ a b) = gatherDelays a <> gatherDelays b
gatherDelays _ = []

codegen :: Box -> IO ()
codegen b = do
  putStrLn $ "out = " <> flow b
  sequence_
    [ putStrLn $ n <> " = " <> flow b'
    | (Ident n, b') <- gatherDelays b
    ]

b1 :: Box
b1 = BFunc "+" (BConst (I 5)) (BVar (Ident "sample_rate"))

b2 :: Box
b2 = res
  where
    prev = BDelay (Ident "prev" ) 1 res
    res = BFunc "+" prev (BConst (I 1))

--------------------------------------------------------------------------------

data Binding expr = Binding Ident expr

-- TODO: streams not in scope outside of graph
-- TODO: branch operation computes both branches

data Index = IConst Number | IVar Ident

data Expr
  = EConst Number
  | EVar Ident           -- references a regular class var, not a graph
  | EGraph Graph         -- ref to other graphs already inlined
  | ESelect Expr [Index]
  | ERec Int Ident [Binding Expr] Expr -- rec delay |prev| -> expr
  | ECall String Expr Expr
  | EArr [Expr]

data Graph = Graph [Binding Expr] Expr

newtype BoxIndex = BoxIndex Int
  deriving Num

data LBox
  = LBConst Number
  | LBVar Ident
  | LBDelay Int BoxIndex
  | LBArr [BoxIndex]
  | LBSelect [BoxIndex] BoxIndex 
  | LBFunc String BoxIndex BoxIndex -- TODO: func must be pure

inlineGraph :: Expr -> [Index] -> (Expr, Maybe (Ident, [Index]))
inlineGraph = undefined

-- TODO: semantic check of no mutual or self recursion between exprs/boxes
inlineExpr :: [Binding Expr] -> Expr -> Expr
inlineExpr = undefined

newBox :: LBox -> State (Map BoxIndex LBox) BoxIndex
newBox = undefined

exprToBoxes :: Map Ident BoxIndex -> Expr -> State (Map BoxIndex LBox) [BoxIndex]
exprToBoxes _ (EConst n) = pure <$> newBox (LBConst n)
exprToBoxes env (EVar n)
  | Just boxIndex <- M.lookup n env = pure [boxIndex]
  | otherwise = pure <$> newBox (LBVar n)
exprToBoxes _ (ERec _ _ _ (EConst n)) = pure <$> newBox (LBConst n)
exprToBoxes env (ERec delay n bindings ret) = do
  -- replace n in bindings and ret with [
  -- TODO: replace leaf values in ret with the delay boxes

  rec
    retBoxes <- exprToBoxes (M.insert n argNode env) ret
    delayBoxes <- traverse newBox $ map (LBDelay delay) retBoxes
    argNode <- newBox (LBArr delayBoxes)

  pure retBoxes

-- TODO: should this be legal: f: f32[4] -> f32, rec |prev| return (f prev)

--------------------------------------------------------------------------------

desugar :: Map Ident Expr -> Graph -> State BoxIndex [LBox]
desugar env (Graph bindings ret) = sequence
  [ undefined
  | Binding n e <- bindings
  ]
  where
    -- TODO no shadowing etc
    innerEnv =  M.fromList
      [ (n, e)
      | Binding n e <- bindings
      ]
