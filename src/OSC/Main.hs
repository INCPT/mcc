module OSC.Main where

import OSC.Transforms.Typecheck
import OSC.Transforms.AnnBind
import OSC.Transforms.FoldSel
import OSC.Transforms.Defunc
import OSC.Codegen

compile2 = program
   where
      (expr, dfm) = defunc $ annCapturedBindings $ foldSelections $ dbgInfer e3
      program = codegen dfm expr