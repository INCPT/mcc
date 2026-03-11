{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module OSC.Box where

import qualified Control.Monad.State as ST
import Control.Monad.State (State)

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

data Binding = Binding Ident Expr

data Array = Array [Int] [Expr] -- dimensions, flat array

data Expr
  = EConst Number
  | EGraph Graph [Int] -- ref to other graphs already inlined; [Int] is the access index
  | EVar Ident
  | ERec Int Ident [Binding] Expr -- rec delay |prev| -> expr
  | EStruct [(String, Expr)]
  | EArr Array

data Graph = Graph [Binding] Array

newtype BoxIndex = BoxIndex Int
  deriving Num

data LBox
  = LBConst Number
  | LBVar Ident
  | LBDelay Ident Int BoxIndex
  | LBFunc String BoxIndex BoxIndex -- TODO: func must be pure

inc :: State BoxIndex BoxIndex
inc = undefined

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
