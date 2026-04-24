module OSC.Main where

import OSC.Expr.Base (Expr (..))
import qualified OSC.Expr.Comp as C
import OSC.Expr.Functors

import OSC.Codegen

import OSC.Transforms.Typecheck
import OSC.Transforms.AnnBind
import OSC.Transforms.FoldSel
import OSC.Transforms.Defunc

import OSC.Pretty

stgCompile expr = prettyString program
   where
      (expr', dfm) = defunc $ annCapturedBindings $ foldSelections $ dbgInfer expr
      program = codegen dfm expr'

stgDefunc = prettyString . defunc . annCapturedBindings . foldSelections . dbgInfer
stgAnn = prettyString . annCapturedBindings . foldSelections . dbgInfer
stgFold = prettyString . foldSelections . dbgInfer
stgTypecheck = prettyString . dbgInfer