module OSC.Main where

import OSC.Transforms.Typecheck
import OSC.Transforms.AnnBind
import OSC.Transforms.FoldSel
import OSC.Transforms.Defunc
import OSC.Codegen

import OSC.Pretty

stgCompile expr = prettyString program
   where
      (expr', dfm) = defunc $ annCapturedBindings $ foldSelections $ dbgInfer expr
      program = codegen dfm expr'

stgDefunc = prettyString . defunc . annCapturedBindings . foldSelections . dbgInfer
stgAnn = prettyString . annCapturedBindings . foldSelections . dbgInfer
stgFold = prettyString . foldSelections . dbgInfer
stgTypecheck = prettyString . dbgInfer