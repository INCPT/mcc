module OSC.Codegen.Interpret where

import OSC.Codegen
import OSC.Codegen.Backend

data Value = VNumber Number | VArr [Value]
  deriving Show

interpretToList :: Int -> IR -> [Ref]
interpretToList steps = undefined