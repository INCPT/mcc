module OSC.Main where

import OSC.Expr.Base
import OSC.Expr.Comp
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

exp1 = Fix {unFix = BExpr (App (Fix {unFix = BExpr (App (Fix {unFix = BLam (Lam (TLam [] (TLam [TLam [] (TArr (TNumber TI64) 2),TNumber TF32,TNumber TI64] (TNumber TF64))) [] [(Ident "a185",Fix {unFix = BExpr (App (Fix {unFix = BLam (Lam (TLam [TLam [TNumber TF64] (TArr (TNumber TF32) 5),TNumber TI32] (TNumber TF32)) [Ident "g162",Ident "a536"] [(Ident "b489",Fix {unFix = BExpr (Const (F32 (-1.0)))}),(Ident "f615",Fix {unFix = BLam (Lam (TLam [TNumber TF64,TNumber TI32,TLam [TNumber TF64,TNumber TF32,TNumber TI32] (TNumber TI32)] (TNumber TF64)) [Ident "g728",Ident "y616",Ident "c529"] [(Ident "z873",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I32 (-2)))},Fix {unFix = BExpr (Const (I32 (-1)))},Fix {unFix = BExpr (Const (I32 (-1)))},Fix {unFix = BExpr (Const (I32 2))},Fix {unFix = BExpr (Const (I32 1))}])})] (Fix {unFix = BExpr (Var (Ident "g728"))}))}),(Ident "f75",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I32 1))},Fix {unFix = BExpr (Var (Ident "a536"))}])})] (Fix {unFix = BExpr (Const (F32 0.8131166))}))}) [Fix {unFix = BLam (Lam (TLam [TNumber TF64] (TArr (TNumber TF32) 5)) [Ident "a701"] [(Ident "b940",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F64 0.6166743461431045))}])}),(Ident "g535",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I64 (-1)))},Fix {unFix = BExpr (Const (I64 2))},Fix {unFix = BExpr (Const (I64 2))}])})] (Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F32 0.52433515))},Fix {unFix = BExpr (Const (F32 1.0))},Fix {unFix = BExpr (Const (F32 0.0))},Fix {unFix = BExpr (Const (F32 (-1.0)))},Fix {unFix = BExpr (Const (F32 0.32553566))}])}))},Fix {unFix = BSelect (Select (Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I32 (-1)))},Fix {unFix = BExpr (Const (I32 (-1)))}])}) (Fix {unFix = BExpr (Const (I32 0))}))}])}),(Ident "g883",Fix {unFix = BExpr (App (Fix {unFix = BLam (Lam (TLam [] (TNumber TF64)) [] [(Ident "f239",Fix {unFix = BExpr (Arr [Fix {unFix = BLam (Lam (TLam [TNumber TF32] (TNumber TI64)) [Ident "y79"] [(Ident "c999",Fix {unFix = BExpr (Const (F64 (-1.0)))})] (Fix {unFix = BExpr (Const (I64 1))}))},Fix {unFix = BLam (Lam (TLam [TNumber TF32] (TNumber TI64)) [Ident "y348"] [(Ident "c221",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I64 1))},Fix {unFix = BExpr (Const (I64 (-1)))},Fix {unFix = BExpr (Const (I64 1))},Fix {unFix = BExpr (Const (I64 (-1)))}])}),(Ident "b515",Fix {unFix = BExpr (Const (I64 1))})] (Fix {unFix = BExpr (Var (Ident "b515"))}))},Fix {unFix = BLam (Lam (TLam [TNumber TF32] (TNumber TI64)) [Ident "b768"] [] (Fix {unFix = BExpr (Const (I64 (-1)))}))},Fix {unFix = BLam (Lam (TLam [TNumber TF32] (TNumber TI64)) [Ident "f577"] [(Ident "f290",Fix {unFix = BLam (Lam (TLam [] (TNumber TF64)) [] [] (Fix {unFix = BExpr (Const (F64 1.0))}))}),(Ident "y511",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F32 0.0))},Fix {unFix = BExpr (Const (F32 0.0))}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F32 (-1.0)))},Fix {unFix = BExpr (Const (F32 (-1.0)))}])}])})] (Fix {unFix = BExpr (Const (I64 (-1)))}))}])})] (Fix {unFix = BExpr (Const (F64 (-1.0)))}))}) [])}),(Ident "g719",Fix {unFix = BExpr (App (Fix {unFix = BExpr (App (Fix {unFix = BLam (Lam (TLam [TNumber TF64,TLam [TNumber TI64,TNumber TF64] (TNumber TF32)] (TLam [] (TLam [] (TNumber TF64)))) [Ident "c70",Ident "f712"] [(Ident "g70",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F32 0.3580764))},Fix {unFix = BExpr (Const (F32 0.660339))},Fix {unFix = BExpr (Var (Ident "a185"))}])})] (Fix {unFix = BLam (Lam (TLam [] (TLam [] (TNumber TF64))) [] [(Ident "b396",Fix {unFix = BExpr (Const (F32 1.0))})] (Fix {unFix = BLam (Lam (TLam [] (TNumber TF64)) [] [(Ident "f74",Fix {unFix = BExpr (Const (F32 0.7508129))})] (Fix {unFix = BExpr (Const (F64 (-1.0)))}))}))}))}) [Fix {unFix = BExpr (Const (F64 (-2.0)))},Fix {unFix = BLam (Lam (TLam [TNumber TI64,TNumber TF64] (TNumber TF32)) [Ident "b858",Ident "z653"] [(Ident "y672",Fix {unFix = BLam (Lam (TLam [] (TNumber TI32)) [] [] (Fix {unFix = BExpr (Const (I32 1))}))}),(Ident "x226",Fix {unFix = BExpr (Const (I32 1))}),(Ident "x867",Fix {unFix = BExpr (Const (F64 0.8983154145194279))})] (Fix {unFix = BExpr (Const (F32 1.0))}))}])}) [])})] (Fix {unFix = BExpr (App (Fix {unFix = BExpr (App (Fix {unFix = BLam (Lam (TLam [TNumber TI32,TNumber TF32,TNumber TI32] (TLam [TNumber TF64,TNumber TI64,TNumber TI64] (TLam [TLam [] (TArr (TNumber TI64) 2),TNumber TF32,TNumber TI64] (TNumber TF64)))) [Ident "z541",Ident "x317",Ident "f146"] [(Ident "b784",Fix {unFix = BLam (Lam (TLam [TArr (TNumber TI32) 3] (TNumber TF32)) [Ident "g468"] [(Ident "b842",Fix {unFix = BExpr (Const (I64 (-1)))}),(Ident "z906",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I64 (-1)))}])})] (Fix {unFix = BExpr (Const (F32 0.0))}))}),(Ident "x625",Fix {unFix = BExpr (Arr [Fix {unFix = BLam (Lam (TLam [] (TNumber TI64)) [] [(Ident "b341",Fix {unFix = BExpr (Const (I64 (-1)))}),(Ident "c490",Fix {unFix = BExpr (Const (I32 1))}),(Ident "g644",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F64 (-1.0)))},Fix {unFix = BExpr (Var (Ident "g883"))},Fix {unFix = BExpr (Const (F64 0.34980493298573934))},Fix {unFix = BExpr (Const (F64 1.0))}])})] (Fix {unFix = BExpr (Const (I64 0))}))}])}),(Ident "x212",Fix {unFix = BExpr (Arr [Fix {unFix = BLam (Lam (TLam [TNumber TI64] (TNumber TF32)) [Ident "g298"] [(Ident "z644",Fix {unFix = BExpr (Const (I64 2))}),(Ident "f77",Fix {unFix = BExpr (Const (I64 (-2)))}),(Ident "g802",Fix {unFix = BLam (Lam (TLam [] (TNumber TI64)) [] [(Ident "f727",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F32 (-1.0)))}])}),(Ident "c540",Fix {unFix = BExpr (Const (F64 (-1.0)))}),(Ident "a413",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I32 2))}])})] (Fix {unFix = BExpr (Const (I64 1))}))})] (Fix {unFix = BExpr (Const (F32 0.9629494))}))},Fix {unFix = BLam (Lam (TLam [TNumber TI64] (TNumber TF32)) [Ident "f745"] [] (Fix {unFix = BExpr (Var (Ident "x317"))}))},Fix {unFix = BLam (Lam (TLam [TNumber TI64] (TNumber TF32)) [Ident "g75"] [(Ident "y79",Fix {unFix = BExpr (Const (I32 1))})] (Fix {unFix = BExpr (Const (F32 0.13820219))}))},Fix {unFix = BLam (Lam (TLam [TNumber TI64] (TNumber TF32)) [Ident "f7"] [] (Fix {unFix = BExpr (Const (F32 0.3802504))}))}])})] (Fix {unFix = BLam (Lam (TLam [TNumber TF64,TNumber TI64,TNumber TI64] (TLam [TLam [] (TArr (TNumber TI64) 2),TNumber TF32,TNumber TI64] (TNumber TF64))) [Ident "c388",Ident "b190",Ident "y134"] [(Ident "c173",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Var (Ident "z541"))},Fix {unFix = BExpr (Var (Ident "f146"))},Fix {unFix = BExpr (Const (I32 (-1)))}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I32 (-1)))},Fix {unFix = BExpr (Const (I32 (-1)))},Fix {unFix = BExpr (Var (Ident "z541"))}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I32 1))},Fix {unFix = BExpr (Const (I32 (-1)))},Fix {unFix = BExpr (Const (I32 (-1)))}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I32 1))},Fix {unFix = BExpr (Const (I32 1))},Fix {unFix = BExpr (Var (Ident "f146"))}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I32 1))},Fix {unFix = BExpr (Var (Ident "z541"))},Fix {unFix = BExpr (Var (Ident "f146"))}])}])})] (Fix {unFix = BLam (Lam (TLam [TLam [] (TArr (TNumber TI64) 2),TNumber TF32,TNumber TI64] (TNumber TF64)) [Ident "y185",Ident "c625",Ident "z659"] [(Ident "y17",Fix {unFix = BLam (Lam (TLam [] (TLam [TNumber TI32,TNumber TF32] (TNumber TI64))) [] [(Ident "y610",Fix {unFix = BExpr (Var (Ident "a185"))})] (Fix {unFix = BLam (Lam (TLam [TNumber TI32,TNumber TF32] (TNumber TI64)) [Ident "z489",Ident "g481"] [(Ident "b306",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F64 (-1.0)))}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F64 (-1.0)))}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F64 0.37655135581812005))}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Var (Ident "g883"))}])}])}),(Ident "c883",Fix {unFix = BExpr (Const (I64 (-1)))})] (Fix {unFix = BExpr (Const (I64 1))}))}))})] (Fix {unFix = BExpr (Const (F64 1.0))}))}))}))}) [Fix {unFix = BExpr (Const (I32 (-1)))},Fix {unFix = BExpr (Const (F32 0.0))},Fix {unFix = BExpr (Const (I32 1))}])}) [Fix {unFix = BExpr (Var (Ident "g883"))},Fix {unFix = BExpr (Op Add (Fix {unFix = BExpr (Const (I64 1))}) (Fix {unFix = BExpr (Const (I64 2))}))},Fix {unFix = BExpr (Const (I64 1))}])}))}) [])}) [Fix {unFix = BLam (Lam (TLam [] (TArr (TNumber TI64) 2)) [] [] (Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I64 1))},Fix {unFix = BExpr (Op Mul (Fix {unFix = BRec (Rec (TNumber TI64) 3 (Ident "c392") [(Ident "z729",Fix {unFix = BExpr (Const (F32 7.0670485e-2))})] (Fix {unFix = BExpr (Op Add (Fix {unFix = BExpr (Var (Ident "c392"))}) (Fix {unFix = BExpr (Var (Ident "c392"))}))}))}) (Fix {unFix = BSelect (Select (Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I64 1))},Fix {unFix = BExpr (Const (I64 0))},Fix {unFix = BExpr (Const (I64 1))},Fix {unFix = BExpr (Const (I64 0))}])}) (Fix {unFix = BExpr (Const (I32 0))}))}))}])}))},Fix {unFix = BRec (Rec (TNumber TF32) 1 (Ident "z939") [(Ident "z867",Fix {unFix = BSelect (Select (Fix {unFix = BSelect (Select (Fix {unFix = BExpr (App (Fix {unFix = BLam (Lam (TLam [TLam [TLam [TNumber TI32,TNumber TF64] (TNumber TI32)] (TLam [] (TNumber TF32))] (TArr (TArr (TArr (TNumber TF32) 5) 1) 5)) [Ident "f769"] [(Ident "x916",Fix {unFix = BExpr (Const (I64 1))})] (Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F32 1.0))},Fix {unFix = BExpr (Var (Ident "z939"))},Fix {unFix = BExpr (Const (F32 0.0))},Fix {unFix = BExpr (Const (F32 0.19118917))},Fix {unFix = BExpr (Var (Ident "z939"))}])}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Var (Ident "z939"))},Fix {unFix = BExpr (Const (F32 (-3.0)))},Fix {unFix = BExpr (Var (Ident "z939"))},Fix {unFix = BExpr (Const (F32 1.0))},Fix {unFix = BExpr (Const (F32 (-1.0)))}])}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F32 0.55067223))},Fix {unFix = BExpr (Const (F32 0.0))},Fix {unFix = BExpr (Var (Ident "z939"))},Fix {unFix = BExpr (Var (Ident "b380"))},Fix {unFix = BExpr (Const (F32 (-1.0)))}])}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Var (Ident "b380"))},Fix {unFix = BExpr (Const (F32 0.88358927))},Fix {unFix = BExpr (Const (F32 0.34966546))},Fix {unFix = BExpr (Var (Ident "b380"))},Fix {unFix = BExpr (Const (F32 0.82002145))}])}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F32 1.0))},Fix {unFix = BExpr (Const (F32 0.15141553))},Fix {unFix = BExpr (Var (Ident "z939"))},Fix {unFix = BExpr (Const (F32 (-1.0)))},Fix {unFix = BExpr (Const (F32 1.0))}])}])}])}))}) [Fix {unFix = BLam (Lam (TLam [TLam [TNumber TI32,TNumber TF64] (TNumber TI32)] (TLam [] (TNumber TF32))) [Ident "z849"] [] (Fix {unFix = BLam (Lam (TLam [] (TNumber TF32)) [] [(Ident "g855",Fix {unFix = BLam (Lam (TLam [TNumber TF64,TArr (TNumber TF32) 5] (TNumber TF32)) [Ident "y160",Ident "z810"] [(Ident "y736",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Var (Ident "y160"))}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F64 0.3039943970818343))}])}])}),(Ident "z428",Fix {unFix = BExpr (Const (F32 0.32194358))})] (Fix {unFix = BExpr (Const (F32 (-2.0)))}))})] (Fix {unFix = BExpr (Var (Ident "z939"))}))}))}])}) (Fix {unFix = BExpr (Const (I32 1))}))}) (Fix {unFix = BExpr (Const (I32 0))}))}),(Ident "b380",Fix {unFix = BExpr (App (Fix {unFix = BLam (Lam (TLam [TArr (TNumber TF64) 5] (TNumber TF32)) [Ident "x0"] [] (Fix {unFix = BExpr (App (Fix {unFix = BLam (Lam (TLam [TNumber TF64,TArr (TArr (TNumber TF32) 1) 4] (TNumber TF32)) [Ident "x905",Ident "a806"] [] (Fix {unFix = BExpr (Const (F32 0.85035396))}))}) [Fix {unFix = BExpr (Const (F64 0.6046227360502868))},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F32 0.0))}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F32 (-1.0)))}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F32 (-1.0)))}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F32 1.0))}])}])}])}))}) [Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F64 (-1.0)))},Fix {unFix = BExpr (Const (F64 0.6826255995818981))},Fix {unFix = BExpr (Const (F64 0.9430947770439371))},Fix {unFix = BExpr (Const (F64 1.0))},Fix {unFix = BExpr (Const (F64 (-1.0)))}])}])}),(Ident "y635",Fix {unFix = BExpr (Op Xor (Fix {unFix = BRec (Rec (TNumber TI64) 4 (Ident "f604") [(Ident "y690",Fix {unFix = BExpr (Const (I64 0))})] (Fix {unFix = BExpr (Op Add (Fix {unFix = BExpr (Op Sub (Fix {unFix = BExpr (Var (Ident "f604"))}) (Fix {unFix = BExpr (Const (I64 (-1)))}))}) (Fix {unFix = BExpr (Const (I64 0))}))}))}) (Fix {unFix = BExpr (Op Min (Fix {unFix = BExpr (App (Fix {unFix = BLam (Lam (TLam [TLam [] (TNumber TI32)] (TNumber TI64)) [Ident "c141"] [(Ident "a105",Fix {unFix = BExpr (Arr [Fix {unFix = BLam (Lam (TLam [TNumber TI64,TNumber TI32,TNumber TI64] (TNumber TI32)) [Ident "x788",Ident "a136",Ident "g665"] [] (Fix {unFix = BExpr (Const (I32 (-1)))}))},Fix {unFix = BLam (Lam (TLam [TNumber TI64,TNumber TI32,TNumber TI64] (TNumber TI32)) [Ident "c24",Ident "f417",Ident "b977"] [(Ident "c294",Fix {unFix = BExpr (Const (I64 (-1)))}),(Ident "x123",Fix {unFix = BLam (Lam (TLam [TNumber TF64,TNumber TF64,TNumber TF64] (TNumber TF32)) [Ident "f716",Ident "b611",Ident "y697"] [(Ident "c494",Fix {unFix = BLam (Lam (TLam [TNumber TI32] (TLam [] (TNumber TI32))) [Ident "g503"] [] (Fix {unFix = BExpr (Var (Ident "c141"))}))}),(Ident "b775",Fix {unFix = BExpr (Const (F64 0.9446154572749963))}),(Ident "z604",Fix {unFix = BExpr (Const (I64 1))})] (Fix {unFix = BExpr (Const (F32 (-1.0)))}))})] (Fix {unFix = BExpr (Const (I32 (-2)))}))}])}),(Ident "y835",Fix {unFix = BExpr (Const (F32 0.40861344))})] (Fix {unFix = BExpr (Const (I64 1))}))}) [Fix {unFix = BLam (Lam (TLam [] (TNumber TI32)) [] [(Ident "a940",Fix {unFix = BLam (Lam (TLam [TArr (TNumber TF32) 4,TNumber TF32,TLam [TNumber TF64,TNumber TF32,TNumber TF32] (TNumber TI32)] (TNumber TI32)) [Ident "z426",Ident "f521",Ident "b407"] [(Ident "y5",Fix {unFix = BExpr (Const (I32 (-1)))})] (Fix {unFix = BExpr (Var (Ident "y5"))}))})] (Fix {unFix = BExpr (Const (I32 0))}))}])}) (Fix {unFix = BExpr (Op Max (Fix {unFix = BExpr (Const (I64 0))}) (Fix {unFix = BExpr (Const (I64 1))}))}))}))})] (Fix {unFix = BExpr (Op Add (Fix {unFix = BExpr (Op Sub (Fix {unFix = BExpr (Var (Ident "z939"))}) (Fix {unFix = BRec (Rec (TNumber TF32) 3 (Ident "z555") [(Ident "x597",Fix {unFix = BExpr (Const (F32 6.408423e-2))})] (Fix {unFix = BExpr (Op Sub (Fix {unFix = BExpr (Op Add (Fix {unFix = BExpr (Var (Ident "z555"))}) (Fix {unFix = BExpr (Const (F32 0.3114971))}))}) (Fix {unFix = BExpr (Const (F32 1.0))}))}))}))}) (Fix {unFix = BExpr (App (Fix {unFix = BLam (Lam (TLam [] (TNumber TF32)) [] [(Ident "x809",Fix {unFix = BExpr (Const (I32 1))})] (Fix {unFix = BExpr (Const (F32 1.0))}))}) [])}))}))},Fix {unFix = BExpr (Op Min (Fix {unFix = BExpr (Const (I64 0))}) (Fix {unFix = BExpr (Op And (Fix {unFix = BExpr (Const (I64 (-2)))}) (Fix {unFix = BExpr (Op Sub (Fix {unFix = BExpr (Const (I64 (-1)))}) (Fix {unFix = BRec (Rec (TNumber TI64) 5 (Ident "a839") [] (Fix {unFix = BExpr (Op Add (Fix {unFix = BExpr (Op Add (Fix {unFix = BExpr (Var (Ident "a839"))}) (Fix {unFix = BExpr (Const (I64 (-3)))}))}) (Fix {unFix = BExpr (Var (Ident "a839"))}))}))}))}))}))}])}
exp2 = Fix {unFix = BExpr (App (Fix {unFix = BExpr (App (Fix {unFix = BLam (Lam (TLam [] (TLam [TLam [] (TArr (TNumber TI64) 2),TNumber TF32,TNumber TI64] (TNumber TF64))) [] [(Ident "a185",Fix {unFix = BExpr (App (Fix {unFix = BLam (Lam (TLam [TLam [TNumber TF64] (TArr (TNumber TF32) 5),TNumber TI32] (TNumber TF32)) [Ident "g162",Ident "a536"] [(Ident "b489",Fix {unFix = BExpr (Const (F32 (-1.0)))}),(Ident "f615",Fix {unFix = BLam (Lam (TLam [TNumber TF64,TNumber TI32,TLam [TNumber TF64,TNumber TF32,TNumber TI32] (TNumber TI32)] (TNumber TF64)) [Ident "g728",Ident "y616",Ident "c529"] [(Ident "z873",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I32 (-2)))},Fix {unFix = BExpr (Const (I32 (-1)))},Fix {unFix = BExpr (Const (I32 (-1)))},Fix {unFix = BExpr (Const (I32 2))},Fix {unFix = BExpr (Const (I32 1))}])})] (Fix {unFix = BExpr (Var (Ident "g728"))}))}),(Ident "f75",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I32 1))},Fix {unFix = BExpr (Var (Ident "a536"))}])})] (Fix {unFix = BExpr (Const (F32 0.8131166))}))}) [Fix {unFix = BLam (Lam (TLam [TNumber TF64] (TArr (TNumber TF32) 5)) [Ident "a701"] [(Ident "b940",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F64 0.6166743461431045))}])}),(Ident "g535",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I64 (-1)))},Fix {unFix = BExpr (Const (I64 2))},Fix {unFix = BExpr (Const (I64 2))}])})] (Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F32 0.52433515))},Fix {unFix = BExpr (Const (F32 1.0))},Fix {unFix = BExpr (Const (F32 0.0))},Fix {unFix = BExpr (Const (F32 (-1.0)))},Fix {unFix = BExpr (Const (F32 0.32553566))}])}))},Fix {unFix = BSelect (Select (Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I32 (-1)))},Fix {unFix = BExpr (Const (I32 (-1)))}])}) (Fix {unFix = BExpr (Const (I32 0))}))}])}),(Ident "g883",Fix {unFix = BExpr (App (Fix {unFix = BLam (Lam (TLam [] (TNumber TF64)) [] [(Ident "f239",Fix {unFix = BExpr (Arr [Fix {unFix = BLam (Lam (TLam [TNumber TF32] (TNumber TI64)) [Ident "y79"] [(Ident "c999",Fix {unFix = BExpr (Const (F64 (-1.0)))})] (Fix {unFix = BExpr (Const (I64 1))}))},Fix {unFix = BLam (Lam (TLam [TNumber TF32] (TNumber TI64)) [Ident "y348"] [(Ident "c221",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I64 1))},Fix {unFix = BExpr (Const (I64 (-1)))},Fix {unFix = BExpr (Const (I64 1))},Fix {unFix = BExpr (Const (I64 (-1)))}])}),(Ident "b515",Fix {unFix = BExpr (Const (I64 1))})] (Fix {unFix = BExpr (Var (Ident "b515"))}))},Fix {unFix = BLam (Lam (TLam [TNumber TF32] (TNumber TI64)) [Ident "b768"] [] (Fix {unFix = BExpr (Const (I64 (-1)))}))},Fix {unFix = BLam (Lam (TLam [TNumber TF32] (TNumber TI64)) [Ident "f577"] [(Ident "f290",Fix {unFix = BLam (Lam (TLam [] (TNumber TF64)) [] [] (Fix {unFix = BExpr (Const (F64 1.0))}))}),(Ident "y511",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F32 0.0))},Fix {unFix = BExpr (Const (F32 0.0))}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F32 (-1.0)))},Fix {unFix = BExpr (Const (F32 (-1.0)))}])}])})] (Fix {unFix = BExpr (Const (I64 (-1)))}))}])})] (Fix {unFix = BExpr (Const (F64 (-1.0)))}))}) [])}),(Ident "g719",Fix {unFix = BExpr (App (Fix {unFix = BExpr (App (Fix {unFix = BLam (Lam (TLam [TNumber TF64,TLam [TNumber TI64,TNumber TF64] (TNumber TF32)] (TLam [] (TLam [] (TNumber TF64)))) [Ident "c70",Ident "f712"] [(Ident "g70",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F32 0.3580764))},Fix {unFix = BExpr (Const (F32 0.660339))},Fix {unFix = BExpr (Var (Ident "a185"))}])})] (Fix {unFix = BLam (Lam (TLam [] (TLam [] (TNumber TF64))) [] [(Ident "b396",Fix {unFix = BExpr (Const (F32 1.0))})] (Fix {unFix = BLam (Lam (TLam [] (TNumber TF64)) [] [(Ident "f74",Fix {unFix = BExpr (Const (F32 0.7508129))})] (Fix {unFix = BExpr (Const (F64 (-1.0)))}))}))}))}) [Fix {unFix = BExpr (Const (F64 (-2.0)))},Fix {unFix = BLam (Lam (TLam [TNumber TI64,TNumber TF64] (TNumber TF32)) [Ident "b858",Ident "z653"] [(Ident "y672",Fix {unFix = BLam (Lam (TLam [] (TNumber TI32)) [] [] (Fix {unFix = BExpr (Const (I32 1))}))}),(Ident "x226",Fix {unFix = BExpr (Const (I32 1))}),(Ident "x867",Fix {unFix = BExpr (Const (F64 0.8983154145194279))})] (Fix {unFix = BExpr (Const (F32 1.0))}))}])}) [])})] (Fix {unFix = BExpr (App (Fix {unFix = BExpr (App (Fix {unFix = BLam (Lam (TLam [TNumber TI32,TNumber TF32,TNumber TI32] (TLam [TNumber TF64,TNumber TI64,TNumber TI64] (TLam [TLam [] (TArr (TNumber TI64) 2),TNumber TF32,TNumber TI64] (TNumber TF64)))) [Ident "z541",Ident "x317",Ident "f146"] [(Ident "b784",Fix {unFix = BLam (Lam (TLam [TArr (TNumber TI32) 3] (TNumber TF32)) [Ident "g468"] [(Ident "b842",Fix {unFix = BExpr (Const (I64 (-1)))}),(Ident "z906",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I64 (-1)))}])})] (Fix {unFix = BExpr (Const (F32 0.0))}))}),(Ident "x625",Fix {unFix = BExpr (Arr [Fix {unFix = BLam (Lam (TLam [] (TNumber TI64)) [] [(Ident "b341",Fix {unFix = BExpr (Const (I64 (-1)))}),(Ident "c490",Fix {unFix = BExpr (Const (I32 1))}),(Ident "g644",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F64 (-1.0)))},Fix {unFix = BExpr (Var (Ident "g883"))},Fix {unFix = BExpr (Const (F64 0.34980493298573934))},Fix {unFix = BExpr (Const (F64 1.0))}])})] (Fix {unFix = BExpr (Const (I64 0))}))}])}),(Ident "x212",Fix {unFix = BExpr (Arr [Fix {unFix = BLam (Lam (TLam [TNumber TI64] (TNumber TF32)) [Ident "g298"] [(Ident "z644",Fix {unFix = BExpr (Const (I64 2))}),(Ident "f77",Fix {unFix = BExpr (Const (I64 (-2)))}),(Ident "g802",Fix {unFix = BLam (Lam (TLam [] (TNumber TI64)) [] [(Ident "f727",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F32 (-1.0)))}])}),(Ident "c540",Fix {unFix = BExpr (Const (F64 (-1.0)))}),(Ident "a413",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I32 2))}])})] (Fix {unFix = BExpr (Const (I64 1))}))})] (Fix {unFix = BExpr (Const (F32 0.9629494))}))},Fix {unFix = BLam (Lam (TLam [TNumber TI64] (TNumber TF32)) [Ident "f745"] [] (Fix {unFix = BExpr (Var (Ident "x317"))}))},Fix {unFix = BLam (Lam (TLam [TNumber TI64] (TNumber TF32)) [Ident "g75"] [(Ident "y79",Fix {unFix = BExpr (Const (I32 1))})] (Fix {unFix = BExpr (Const (F32 0.13820219))}))},Fix {unFix = BLam (Lam (TLam [TNumber TI64] (TNumber TF32)) [Ident "f7"] [] (Fix {unFix = BExpr (Const (F32 0.3802504))}))}])})] (Fix {unFix = BLam (Lam (TLam [TNumber TF64,TNumber TI64,TNumber TI64] (TLam [TLam [] (TArr (TNumber TI64) 2),TNumber TF32,TNumber TI64] (TNumber TF64))) [Ident "c388",Ident "b190",Ident "y134"] [(Ident "c173",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Var (Ident "z541"))},Fix {unFix = BExpr (Var (Ident "f146"))},Fix {unFix = BExpr (Const (I32 (-1)))}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I32 (-1)))},Fix {unFix = BExpr (Const (I32 (-1)))},Fix {unFix = BExpr (Var (Ident "z541"))}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I32 1))},Fix {unFix = BExpr (Const (I32 (-1)))},Fix {unFix = BExpr (Const (I32 (-1)))}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I32 1))},Fix {unFix = BExpr (Const (I32 1))},Fix {unFix = BExpr (Var (Ident "f146"))}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I32 1))},Fix {unFix = BExpr (Var (Ident "z541"))},Fix {unFix = BExpr (Var (Ident "f146"))}])}])})] (Fix {unFix = BLam (Lam (TLam [TLam [] (TArr (TNumber TI64) 2),TNumber TF32,TNumber TI64] (TNumber TF64)) [Ident "y185",Ident "c625",Ident "z659"] [(Ident "y17",Fix {unFix = BLam (Lam (TLam [] (TLam [TNumber TI32,TNumber TF32] (TNumber TI64))) [] [(Ident "y610",Fix {unFix = BExpr (Var (Ident "a185"))})] (Fix {unFix = BLam (Lam (TLam [TNumber TI32,TNumber TF32] (TNumber TI64)) [Ident "z489",Ident "g481"] [(Ident "b306",Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F64 (-1.0)))}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F64 (-1.0)))}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (F64 0.37655135581812005))}])},Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Var (Ident "g883"))}])}])}),(Ident "c883",Fix {unFix = BExpr (Const (I64 (-1)))})] (Fix {unFix = BExpr (Const (I64 1))}))}))})] (Fix {unFix = BExpr (Const (F64 1.0))}))}))}))}) [Fix {unFix = BExpr (Const (I32 (-1)))},Fix {unFix = BExpr (Const (F32 0.0))},Fix {unFix = BExpr (Const (I32 1))}])}) [Fix {unFix = BExpr (Var (Ident "g883"))},Fix {unFix = BExpr (Op Add (Fix {unFix = BExpr (Const (I64 1))}) (Fix {unFix = BExpr (Const (I64 2))}))},Fix {unFix = BExpr (Const (I64 1))}])}))}) [])}) [Fix {unFix = BLam (Lam (TLam [] (TArr (TNumber TI64) 2)) [] [] (Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I64 1))},Fix {unFix = BExpr (Op Mul (Fix {unFix = BRec (Rec (TNumber TI64) 3 (Ident "c392") [(Ident "z729",Fix {unFix = BExpr (Const (F32 7.0670485e-2))})] (Fix {unFix = BExpr (Op Add (Fix {unFix = BExpr (Var (Ident "c392"))}) (Fix {unFix = BExpr (Var (Ident "c392"))}))}))}) (Fix {unFix = BSelect (Select (Fix {unFix = BExpr (Arr [Fix {unFix = BExpr (Const (I64 1))},Fix {unFix = BExpr (Const (I64 0))},Fix {unFix = BExpr (Const (I64 1))},Fix {unFix = BExpr (Const (I64 0))}])}) (Fix {unFix = BExpr (Const (I32 0))}))}))}])}))},Fix {unFix = BRec (Rec (TNumber TF32) 1 (Ident "z939") [] (Fix {unFix = BExpr (Op Add (Fix {unFix = BExpr (Op Sub (Fix {unFix = BExpr (Var (Ident "z939"))}) (Fix {unFix = BRec (Rec (TNumber TF32) 3 (Ident "z555") [(Ident "x597",Fix {unFix = BExpr (Const (F32 6.408423e-2))})] (Fix {unFix = BExpr (Op Sub (Fix {unFix = BExpr (Op Add (Fix {unFix = BExpr (Var (Ident "z555"))}) (Fix {unFix = BExpr (Const (F32 0.3114971))}))}) (Fix {unFix = BExpr (Const (F32 1.0))}))}))}))}) (Fix {unFix = BExpr (App (Fix {unFix = BLam (Lam (TLam [] (TNumber TF32)) [] [(Ident "x809",Fix {unFix = BExpr (Const (I32 1))})] (Fix {unFix = BExpr (Const (F32 1.0))}))}) [])}))}))},Fix {unFix = BExpr (Op Min (Fix {unFix = BExpr (Const (I64 0))}) (Fix {unFix = BExpr (Op And (Fix {unFix = BExpr (Const (I64 (-2)))}) (Fix {unFix = BExpr (Op Sub (Fix {unFix = BExpr (Const (I64 (-1)))}) (Fix {unFix = BRec (Rec (TNumber TI64) 5 (Ident "a839") [] (Fix {unFix = BExpr (Op Add (Fix {unFix = BExpr (Op Add (Fix {unFix = BExpr (Var (Ident "a839"))}) (Fix {unFix = BExpr (Const (I64 (-3)))}))}) (Fix {unFix = BExpr (Var (Ident "a839"))}))}))}))}))}))}])}

{-

(app (app (lambda (-> () (-> ((-> () (arr i64 2)) f32 i64) f64))
  (params ())
  (bindings
    (a185 (app (lambda (-> ((-> (f64) (arr f32 5)) i32) f32)
      (params (g162 a536))
      (bindings
        (b489 -1.0:f32)
        (f615 (lambda (-> (f64 i32 (-> (f64 f32 i32) i32)) f64)
          (params (g728 y616 c529))
          (bindings
            (z873 (arr (-2:i32 -1:i32 -1:i32 2:i32 1:i32))))

            g728))
        (f75 (arr (1:i32 a536))))

        0.8131166:f32) ((lambda (-> (f64) (arr f32 5))
      (params (a701))
      (bindings
        (b940 (arr (0.6166743461431045:f64)))
        (g535 (arr (-1:i64 2:i64 2:i64))))

        (arr (0.52433515:f32 1.0:f32 0.0:f32 -1.0:f32 0.32553566:f32))) (select (arr (-1:i32 -1:i32)) 0:i32))))
    (g719 (app (app (lambda (-> (f64 (-> (i64 f64) f32)) (-> () (-> () f64)))
      (params (c70 f712))
      (bindings
        (g70 (arr (0.3580764:f32 0.660339:f32 a185))))

        (lambda (-> () (-> () f64))
            (params ())
            (bindings
              (b396 1.0:f32))

              (lambda (-> () f64)
                  (params ())
                  (bindings
                    (f74 0.7508129:f32))

                    -1.0:f64))) (-2.0:f64 (lambda (-> (i64 f64) f32)
      (params (b858 z653))
      (bindings
        (x226 1:i32)
        (x867 0.8983154145194279:f64)
        (y672 (lambda (-> () i32)
          (params ())
          (bindings
            )

            1:i32)))

        1.0:f32))) ()))
    (g883 (app (lambda (-> () f64)
      (params ())
      (bindings
        (f239 (arr ((lambda (-> (f32) i64)
          (params (y79))
          (bindings
            (c999 -1.0:f64))

            1:i64) (lambda (-> (f32) i64)
          (params (y348))
          (bindings
            (b515 1:i64)
            (c221 (arr (1:i64 -1:i64 1:i64 -1:i64))))

            b515) (lambda (-> (f32) i64)
          (params (b768))
          (bindings
            )

            -1:i64) (lambda (-> (f32) i64)
          (params (f577))
          (bindings
            (f290 (lambda (-> () f64)
              (params ())
              (bindings
                )

                1.0:f64))
            (y511 (arr ((arr (0.0:f32 0.0:f32)) (arr (-1.0:f32 -1.0:f32))))))

            -1:i64)))))

        -1.0:f64) ())))

    (app (app (lambda (-> (i32 f32 i32) (-> (f64 i64 i64) (-> ((-> () (arr i64 2)) f32 i64) f64)))
        (params (z541 x317 f146))
        (bindings
          (b784 (lambda (-> ((arr i32 3)) f32)
            (params (g468))
            (bindings
              (b842 -1:i64)
              (z906 (arr (-1:i64))))

              0.0:f32))
          (x212 (arr ((lambda (-> (i64) f32)
            (params (g298))
            (bindings
              (f77 -2:i64)
              (g802 (lambda (-> () i64)
                (params ())
                (bindings
                  (a413 (arr (2:i32)))
                  (c540 -1.0:f64)
                  (f727 (arr (-1.0:f32))))

                  1:i64))
              (z644 2:i64))

              0.9629494:f32) (lambda (-> (i64) f32)
            (params (f745))
            (bindings
              )

              x317) (lambda (-> (i64) f32)
            (params (g75))
            (bindings
              (y79 1:i32))

              0.13820219:f32) (lambda (-> (i64) f32)
            (params (f7))
            (bindings
              )

              0.3802504:f32))))
          (x625 (arr ((lambda (-> () i64)
            (params ())
            (bindings
              (b341 -1:i64)
              (c490 1:i32)
              (g644 (arr (-1.0:f64 g883 0.34980493298573934:f64 1.0:f64))))

              0:i64)))))

          (lambda (-> (f64 i64 i64) (-> ((-> () (arr i64 2)) f32 i64) f64))
              (params (c388 b190 y134))
              (bindings
                (c173 (arr ((arr (z541 f146 -1:i32)) (arr (-1:i32 -1:i32 z541)) (arr (1:i32 -1:i32 -1:i32)) (arr (1:i32 1:i32 f146)) (arr (1:i32 z541 f146))))))

                (lambda (-> ((-> () (arr i64 2)) f32 i64) f64)
                    (params (y185 c625 z659))
                    (bindings
                      (y17 (lambda (-> () (-> (i32 f32) i64))
                        (params ())
                        (bindings
                          (y610 a185))

                          (lambda (-> (i32 f32) i64)
                              (params (z489 g481))
                              (bindings
                                (b306 (arr ((arr (-1.0:f64)) (arr (-1.0:f64)) (arr (0.37655135581812005:f64)) (arr (g883)))))
                                (c883 -1:i64))

                                1:i64))))

                      1.0:f64))) (-1:i32 0.0:f32 1:i32)) (g883 (+ 1:i64 2:i64) 1:i64))) ()) ((lambda (-> () (arr i64 2))
  (params ())
  (bindings
    )

    (arr (1:i64 (* (rec i64 3 c392
        (bindings
            (z729 7.0670485e-2:f32))

          (+ c392 c392)) (select (arr (1:i64 0:i64 1:i64 0:i64)) 0:i32))))) (rec f32 1 z939
  (bindings
      (b380 (app (lambda (-> ((arr f64 5)) f32)
        (params (x0))
        (bindings
          )

          (app (lambda (-> (f64 (arr (arr f32 1) 4)) f32)
              (params (x905 a806))
              (bindings
                )

                0.85035396:f32) (0.6046227360502868:f64 (arr ((arr (0.0:f32)) (arr (-1.0:f32)) (arr (-1.0:f32)) (arr (1.0:f32))))))) ((arr (-1.0:f64 0.6826255995818981:f64 0.9430947770439371:f64 1.0:f64 -1.0:f64)))))
      (y635 (xor (rec i64 4 f604
        (bindings
            (y690 0:i64))

          (+ (- f604 -1:i64) 0:i64)) (min (app (lambda (-> ((-> () i32)) i64)
        (params (c141))
        (bindings
          (a105 (arr ((lambda (-> (i64 i32 i64) i32)
            (params (x788 a136 g665))
            (bindings
              )

              -1:i32) (lambda (-> (i64 i32 i64) i32)
            (params (c24 f417 b977))
            (bindings
              (c294 -1:i64)
              (x123 (lambda (-> (f64 f64 f64) f32)
                (params (f716 b611 y697))
                (bindings
                  (b775 0.9446154572749963:f64)
                  (c494 (lambda (-> (i32) (-> () i32))
                    (params (g503))
                    (bindings
                      )

                      c141))
                  (z604 1:i64))

                  -1.0:f32)))

              -2:i32))))
          (y835 0.40861344:f32))

          1:i64) ((lambda (-> () i32)
        (params ())
        (bindings
          (a940 (lambda (-> ((arr f32 4) f32 (-> (f64 f32 f32) i32)) i32)
            (params (z426 f521 b407))
            (bindings
              (y5 -1:i32))

              y5)))

          0:i32))) (max 0:i64 1:i64))))
      (z867 (select (select (app (lambda (-> ((-> ((-> (i32 f64) i32)) (-> () f32))) (arr (arr (arr f32 5) 1) 5))
        (params (f769))
        (bindings
          (x916 1:i64))

          (arr ((arr ((arr (1.0:f32 z939 0.0:f32 0.19118917:f32 z939)))) (arr ((arr (z939 -3.0:f32 z939 1.0:f32 -1.0:f32)))) (arr ((arr (0.55067223:f32 0.0:f32 z939 b380 -1.0:f32)))) (arr ((arr (b380 0.88358927:f32 0.34966546:f32 b380 0.82002145:f32)))) (arr ((arr (1.0:f32 0.15141553:f32 z939 -1.0:f32 1.0:f32))))))) ((lambda (-> ((-> (i32 f64) i32)) (-> () f32))
        (params (z849))
        (bindings
          )

          (lambda (-> () f32)
              (params ())
              (bindings
                (g855 (lambda (-> (f64 (arr f32 5)) f32)
                  (params (y160 z810))
                  (bindings
                    (y736 (arr ((arr (y160)) (arr (0.3039943970818343:f64)))))
                    (z428 0.32194358:f32))

                    -2.0:f32)))

                z939)))) 1:i32) 0:i32)))

    (+ (- z939 (rec f32 3 z555
        (bindings
            (x597 6.408423e-2:f32))

          (- (+ z555 0.3114971:f32) 1.0:f32))) (app (lambda (-> () f32)
        (params ())
        (bindings
          (x809 1:i32))

          1.0:f32) ()))) (min 0:i64 (and -2:i64 (- -1:i64 (rec i64 5 a839
  (bindings
      )

    (+ (+ a839 -3:i64) a839)))))))

-}