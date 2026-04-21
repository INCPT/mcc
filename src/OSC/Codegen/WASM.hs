module OSC.Codegen.WASM where

data Config = Config
  { smallArrayMaxLength :: Int -- | Small arrays are returned on the stack
  }

{-
  where
    needsStackMap :: Map FuncRef Bool
    needsStackMap = fmap funcNeedsStack dfm.funcMap
      where
        funcNeedsStack (C.LamAnn typ _ bindings body) = or
          [ C.sizeOfType typ > cfg.smallArrayMaxLength
          , or [ M.findWithDefault False fr needsStackMap | Func fr <- universe body ]
          , or [ M.findWithDefault False fr needsStackMap | (_, _, bbody) <- bindings, Func fr <- universe bbody ]
          ]
-}