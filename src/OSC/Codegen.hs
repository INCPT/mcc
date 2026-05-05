{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RecursiveDo #-}

module OSC.Codegen where

import Control.Monad (when)
import Control.Monad.Trans (lift)
import qualified Control.Monad.Reader as R
import Control.Monad.Reader (ReaderT, local, asks, ask, runReaderT)
import Control.Monad.State.Lazy (State, state, runState)
import Control.Monad.Trans.Writer (WriterT, runWriterT, tell)
import qualified Control.Monad.Trans.Writer as W
import Data.Map (Map)
import Data.List (intercalate)
import qualified Data.Map as M
import Prettyprinter (Pretty(..), (<+>), vsep, hsep, parens, brackets, indent)

import OSC.Expr.Comp (Captured, Type (..), TNumber (..), Number (..), Op (..))
import qualified OSC.Expr.Comp as C
import OSC.Expr.Functors
import OSC.Expr.Defunc hiding (const)


newtype Location = Location Int
  deriving (Eq, Ord, Show)

data Ref
  = RConst Number
  | RRet Type
  | RArg Type Captured
  | RVar Type Location
  | RProj {- expression -} Ref {- index -} Ref {- inner dimension, e.g. for the array[4][7], array[1] would set the inner dimension to 7 -} Int
  | RFuncRef FuncRef
  deriving Show

data SliceRoot = SArg Captured | SVar Location | SRet
  deriving Show

data Slice
  = SConst Number
  | SSlice Type {- arg or var or ret -} SliceRoot {- offset -} (Either Int Location) {- length -} Int
  | SFuncRef FuncRef
  deriving Show

data Instruction
  = ICopy {- dest -} Slice {- source -} Slice
  | IIf Slice [Instruction] [Instruction]
  | ICall {- return ref -} Slice {- funcref -} Slice [Slice]
  | IBinOp Op {- result -} Slice {- a -} Slice {- b -} Slice
  | IFor {- counter -} Location {- initial -} Int {- steps -} Int {- step -} Int [Instruction]
  deriving Show

-- PIPELINE --------------------------------------------------------------------

---- [] compile time constant folding (e.g. $voices etc)
---- [-] typecheck [-range propagation]
---- [] float independent computations out of rec blocks
---- [] until fixpoint
------ [] fusion/simplifications
-------- [] eval or unroll small SOACs (when unrolling compute the total number of iterations (e.g. nested SOACs can explode))
-------- [] calculate const expressions
-------- [] elim static indices [a, b, c][1] == b, { x: a, y: 6 }.x == a
-------- [] rec |...| 5.0 == 5.0
-------- [] (|a, b| a + b)(x, y) == x + y
-------- [] fuse SOACs
-------- [] ...
------ [] dead code elim
------ [] CSE (expression should hash to the same hash if e.g. bindings are reordered)
------ [] inline (awlays inline if something used only once, otherwise heuristic)
---- [] float pure expression to the topmost lambda that contains them (e.g. constant arrays will be allocated at the topmost level and become right folded selections)
---- [] float KR/AR to the topmost lambda that contains them
---- [+] ann binds
---- [+] fold selections
---- [] backend
------ [] WASM
-------- [] arrays with constants go into data sections
-------- [] simple return values on stack, arrays in linear mem
-------- [] assign array allocations
---------- [] if elems < N (8-16?) - nested ifs
---------- [] otherwise - br_table jumps
-------- [] allocate globals or locals per function (align at 4/8 bytes)
-------- [] propagate shadow stack pointers to functions that need it (e.g. if they return an array or a binding is an array or a subfunction returns an array (also transitively))

--------------------------------------------------------------------------------

data RecEnv = RecEnv
  { delayBuffer :: Ref
  , writeIdx :: Ref
  , readIdx :: Ref
  }

data Env = Env
  { varMap :: Map Captured Ref
  , recMap :: Map Captured RecEnv
  }

type AllocM = State (Int, Map Location Type)

type CodegenM = ReaderT Env (WriterT [Instruction] AllocM)

allocLoc :: Type -> AllocM Location
allocLoc typ = state $ \(idx, m) -> (Location idx, (idx + 1, M.insert (Location idx) typ m))

alloc :: Type -> CodegenM Ref
alloc typ = fmap (RVar typ) $ lift $ lift $ allocLoc typ

-- array[5][6][3]
-- array[2] :: array[6][3] so slice length is 6 * 3 and offset is 2 * 6 * 3
-- array[2][4] :: array[3] so slice length is 3 and offset is 2 * 6 * 3 + 4 * 3 or (2 * 6 + 4) * 3

-- array[6][3]
-- array[2] :: array[3] so slice length is 3 and offset is 2 * 3

-- array[3]
-- array[2] :: i32 (for example) so slice length is 1 and offset is 2 * 1

toSlice :: Ref -> CodegenM Slice
toSlice (RConst n) = pure $ SConst n
toSlice (RFuncRef fr) = pure $ SFuncRef fr
toSlice (RArg typ arg) = pure $ SSlice typ (SArg arg) (Left 0) (C.elemCountOfType typ)
toSlice (RVar typ loc) = pure $ SSlice typ (SVar loc) (Left 0) (C.elemCountOfType typ)
toSlice (RRet typ) = pure $ SSlice typ SRet (Left 0) (C.elemCountOfType typ)
toSlice (RProj ref idx innerDim) = do
  slice <- toSlice ref
  idxSlice <- toSlice idx
  
  case (slice, idxSlice) of
    -- Constant index with constant offset - compute statically
    (SSlice typ loc (Left offset) _, SConst (I32 i)) ->
      pure $ SSlice typ loc (Left (offset + i * innerDim)) innerDim
    (SSlice typ loc (Left offset) _, SConst (I64 i)) ->
      pure $ SSlice typ loc (Left (offset + i * innerDim)) innerDim
    
    -- Dynamic cases - need to compute offset at runtime
    (SSlice typ loc baseOffset _, _) -> do
      offsetLoc <- lift $ lift $ allocLoc C.ti32
      let offsetVar = RVar C.ti32 offsetLoc

      -- Load index into offset variable
      case idxSlice of
        SConst n
          | C.numberType n == TNumber TI32 -> copyRef offsetVar (RConst n)
        SSlice (TNumber TI32) (SArg arg) (Left 0) 1 -> copyRef offsetVar (RArg C.ti32 arg)
        SSlice (TNumber TI32) (SVar loc) (Left 0) 1 -> copyRef offsetVar (RVar C.ti32 loc)
        _ -> error $ "toSlice: unexpected index slice type: " <> show idxSlice
      
      -- Multiply by inner dimension
      binOp Mul offsetVar (RConst $ I32 innerDim) offsetVar
      
      -- Add base offset
      case baseOffset of
        Left offset -> when (offset /= 0) $ do
          binOp Add offsetVar (RConst $ I32 offset) offsetVar
        Right baseLoc -> do
          binOp Add offsetVar (RVar C.ti32 baseLoc) offsetVar
      
      pure $ SSlice typ loc (Right offsetLoc) innerDim
    
    _ -> error "toSlice: projection of non-variable slice"

copyRef :: Ref -> Ref -> CodegenM ()
copyRef dst src = do
  dstSlice <- toSlice dst
  srcSlice <- toSlice src
  
  lift $ tell [ICopy dstSlice srcSlice]

binOp :: Op -> Ref -> Ref -> Ref -> CodegenM ()
binOp op dest a b = do
  destSlice <- toSlice dest
  aSlice <- toSlice a
  bSlice <- toSlice b
  lift $ tell [IBinOp op destSlice aSlice bSlice]

call :: Ref -> Ref -> [Ref] -> CodegenM ()
call dest funcRef args = do
  destSlice <- toSlice dest
  funcRefSlice <- toSlice funcRef
  argSlices <- traverse toSlice args
  lift $ tell [ICall destSlice funcRefSlice argSlices]

if_ :: Ref -> CodegenM () -> CodegenM () -> CodegenM ()
if_ cond t e = do
  env <- ask
  ((), t') <- lift $ lift $ runWriterT $ runReaderT t env
  ((), e') <- lift $ lift $ runWriterT $ runReaderT e env
  condSlice <- toSlice cond
  lift $ tell [IIf condSlice t' e']

innerDims :: Type -> [Int]
innerDims (TArr (TArr t dim) _) = dim:innerDims t
innerDims (TArr _ _) = [1]
innerDims _ = []

data ProgramFunc = ProgramFunc
  { params :: [(Captured, C.AllocRegion, Type)]
  , locals :: Map Location Type
  , instructions :: [Instruction]
  } deriving Show

data Program = Program
  { globals :: Map Location Type
  , funcMap :: Map FuncRef ProgramFunc
  , tick :: [Instruction]
  , startup :: [Instruction]
  , ref :: Ref
  } deriving Show

--------------------------------------------------------------------------------

codegen :: DefuncMap (Ann Type) -> Ann Type Expr -> Program
codegen dfm expr = Program {..}
  where
    lookupE e k m = case M.lookup k m of
      Just v -> v
      Nothing -> error e

    (((tick, funcMap, ref), startup), (_, globals)) = flip runState (0, mempty) $ runWriterT top

    top = do
      lamAllocs <- mconcat <$> traverse (lift . collectLamAllocations) (M.elems dfm.funcMap)
      (recAllocs, recEnvs) <- mconcat <$> traverse (lift . collectRecAllocations) dfm.recs
  
      let env = Env { varMap = lamAllocs <> recAllocs, recMap = recEnvs }
  
      ((), tick) <- lift $ W.runWriterT $ flip R.runReaderT env $ sequence_ [ genRec rec_ | rec_ <- dfm.recs ]

      let funcMap = fmap (genLam env) dfm.funcMap
  
      ref <- flip R.runReaderT env $ rhs expr
      pure (tick, funcMap, ref)

    collectLamAllocations :: C.LamAnn (Ann Type Expr) -> AllocM (Map Captured Ref)
    collectLamAllocations (C.LamAnn typ params bindings _) = fmap M.fromList $ sequence $ mconcat
      [ [ do
            loc <- allocLoc typ
            pure (n, RVar typ loc)
        | (n, C.AllocGlobal, Ann (typ, _)) <- bindings
        ]
      , [ do
            loc <- allocLoc typ
            pure (n, RVar typ loc)
        | ((n, C.AllocGlobal), typ) <- zip params (C.paramTypes "collecLamAllocations" typ)
        ]
      ]

    collectRecAllocations :: C.RecAnn (Ann Type Expr) -> AllocM (Map Captured Ref, Map Captured RecEnv)
    collectRecAllocations (C.RecAnn typ delay param bindings _) = do
      varMap <- sequence
        [ do
            loc <- allocLoc typ
            pure (n, RVar typ loc)
        | (n, C.AllocGlobal, Ann (typ, _)) <- bindings
        ]

      delayBuffer <- RVar (TArr typ delay) <$> allocLoc (TArr typ delay)
      writeIdx <- RVar C.ti32 <$> allocLoc C.ti32
      readIdx <- RVar C.ti32 <$> allocLoc C.ti32

      pure (M.fromList ((param, RProj delayBuffer readIdx 1):varMap), M.singleton param (RecEnv {..}))

    genLam :: Env -> C.LamAnn (Ann Type Expr) -> ProgramFunc
    genLam env lam@(C.LamAnn typ params_ _ _) = ProgramFunc {..}
      where
        params = [ (n, region, typ) | ((n, region), typ) <- zip params_ (C.paramTypes "genLam" typ) ]
        ((_, instructions), (_, locals)) = flip runState (0, mempty) $ W.runWriterT $ flip runReaderT env (genLam_ lam)

    genLam_ :: C.LamAnn (Ann Type Expr) -> CodegenM ()
    genLam_ (C.LamAnn typ params bindings body) = mdo
       bindingVars <- mconcat <$> sequence
         -- Arguments
         [ M.fromList <$> sequence
              [ do
                  when (region == C.AllocGlobal) $ do
                    var <- asks ((lookupE "genLam_: global" p) . (.varMap))
                    copyRef var (RArg typ p)

                  pure (p, RArg typ p)
              | ((p, region), typ) <- zip params (C.paramTypes "genLam" typ)
              ]

         -- Bindings (must be in topsort order)
         , M.fromList <$> sequence
             [ case region of
                 C.AllocLocal -> do
                   var <- alloc typ
                   local withBindingVars $ gen var bbody
                   pure (n, var)
                 C.AllocGlobal -> do
                   -- Set global ref as return value for binding rhs
                   var <- asks ((lookupE "genLam_: global" n) . (.varMap))
                   local withBindingVars $ gen var bbody
                   pure (n, var)
             | (n, region, bbody@(Ann (typ, _))) <- bindings
             ]
         ]

       let withBindingVars :: Env -> Env
           withBindingVars Env {..} = Env { varMap = bindingVars <> varMap, .. }

       local withBindingVars $ gen (RRet $ C.returnType typ) body

    genRec :: C.RecAnn (Ann Type Expr) -> CodegenM ()
    genRec (C.RecAnn _ delay param bindings body) = do
      env <- ask
      let recEnv = lookupE "genRec: param" param env.recMap

      mdo
        bindingVars <- mconcat <$> sequenceA
          [ M.fromList <$> sequenceA [ (n,) <$> local withBindingVars (rhs bbody) | (n, _, bbody) <- bindings ]
          ]

        let withBindingVars :: Env -> Env
            withBindingVars Env {..} = Env { varMap = bindingVars <> varMap, .. }

        local withBindingVars $ gen (RProj recEnv.delayBuffer recEnv.writeIdx 1) body

        -- Increment read & write index
        binOp Add recEnv.writeIdx (RConst $ I32 1) recEnv.writeIdx
        binOp Mod recEnv.writeIdx (RConst $ I32 delay) recEnv.writeIdx
      
        -- TODO: variable delay
        binOp Add recEnv.readIdx (RConst $ I32 1) recEnv.readIdx
        binOp Mod recEnv.readIdx (RConst $ I32 delay) recEnv.readIdx
    
    pfoldedSelectR body@(Ann (bodyTyp, _)) idxs = do
      bodyVar <- alloc bodyTyp
      gen bodyVar body
      idxVars <- traverse rhs idxs
      pure $ foldr (\(idx, dim) body' -> RProj body' idx dim) bodyVar (zip idxVars (scanl1 (*) (innerDims bodyTyp)))

    prec param = do
      env <- ask
      let envRec = lookupE "prec: param" param env.recMap
      pure (RProj envRec.delayBuffer envRec.readIdx 1)

    rhs :: Ann Type Expr -> CodegenM Ref
    rhs (Ann (_, PConst n)) = pure $ RConst n
    rhs (Ann (_, PFunc fr)) = pure $ RFuncRef fr

    rhs (Ann (_, PCVar n)) = ask >>= \env -> pure (lookupE ("rhs: PVar: " <> show n) n env.varMap)

    rhs e@(Ann (typ, PArr _)) = alloc typ >>= \var -> gen var e >> pure var
    rhs e@(Ann (typ, POp _ _ _)) = alloc typ >>= \var -> gen var e >> pure var
    rhs e@(Ann (typ, PApp _ _)) = alloc typ >>= \var -> gen var e >> pure var
    rhs e@(Ann (typ, PFoldedSelectL _ _)) = alloc typ >>= \var -> gen var e >> pure var

    rhs (Ann (_, PFoldedSelectR body idxs)) = pfoldedSelectR body idxs
    rhs (Ann (_, (PRec param))) = prec param

    ---
    
    gen :: Ref -> Ann Type Expr -> CodegenM ()
    gen ret (Ann (_, PConst n)) = copyRef ret (RConst n)
    gen ret (Ann (_, PFunc fr)) = copyRef ret (RFuncRef fr)

    gen ret (Ann (_, PCVar n)) = ask >>= \env -> copyRef ret (lookupE ("gen: PVar: " <> show n) n env.varMap)

    gen ret (Ann (typ, PArr elems)) = do
      let innerDim = product $ innerDims typ
      sequence_
        [ gen (RProj ret (RConst (C.I32 i)) innerDim) elem
        | (i, elem) <- zip [0..] elems
        ]

    gen ret (Ann (_, POp op a b)) = do
      avar <- rhs a
      bvar <- rhs b
      binOp op ret avar bvar

    gen ret (Ann (_, (PApp f args))) = do
      rargs <- traverse rhs args

      case f of
        Ann (_, PFunc fr) -> call ret (RFuncRef fr) rargs
        _ -> do
          fvar <- rhs f
          call ret fvar rargs

    gen ret (Ann (_, (PFoldedSelectL elems idx@(Ann (idxTyp, _))))) = do
      condVar <- alloc C.ti32
      idxVar <- rhs idx

      let mkRef = case idxTyp of
            TNumber TI32 -> RConst . I32
            TNumber TI64 -> RConst . I64
            _ -> error "eqRef"

      -- TODO: binary tree if
      let recIf [] _ = error "recif: no choice (this is a bug)"
          recIf [elem] _ = gen ret elem
          recIf (elem:elems) i = do
            binOp Eq condVar (mkRef i) idxVar
            if_ condVar (gen ret elem) (recIf elems (i + 1))

      recIf elems 0

    gen ret (Ann (_, PFoldedSelectR body idxs)) = copyRef ret =<< pfoldedSelectR body idxs
    gen ret (Ann (_, (PRec param))) = copyRef ret =<< prec param

-- Pretty instances ------------------------------------------------------------

showType :: Type -> String
showType (TNumber TI32) = "i32"
showType (TNumber TF32) = "f32"
showType (TNumber TI64) = "i64"
showType (TNumber TF64) = "f64"
showType (TArr t dim) = showType t <> "[" <> show dim <> "]"
showType (TLam [] retType) = "() -> " <> showType retType
showType (TLam params retType) = 
  "(" <> intercalate ", " (map showType params) <> ") -> " <> showType retType

instance Pretty Ref where
  pretty (RConst n) = pretty n
  pretty (RRet typ) = "ret:" <> pretty (showType typ)
  pretty (RArg typ ident) = "arg:" <> pretty ident <> ":" <> pretty (showType typ)
  pretty (RVar typ (Location loc)) = "var" <> pretty loc <> ":" <> pretty (showType typ)
  pretty (RProj ref idx innerDim) = pretty ref <> brackets (pretty idx <> ":" <> pretty innerDim)
  pretty (RFuncRef (FuncRef i)) = "f" <> pretty i

instance Pretty SliceRoot where
  pretty (SArg ident) = "arg:" <> pretty ident
  pretty (SVar (Location loc)) = "var" <> pretty loc
  pretty SRet = "ret"

instance Pretty Slice where
  pretty (SConst n) = pretty n
  pretty (SSlice typ root (Left offset) len) = 
    pretty root <> brackets (pretty offset <> ".." <> pretty (offset + len)) <> ":" <> pretty (showType typ)
  pretty (SSlice typ root (Right (Location offsetLoc)) len) =
    pretty root <> brackets ("var" <> pretty offsetLoc <> ".." <> "var" <> pretty offsetLoc <> "+" <> pretty len) <> ":" <> pretty (showType typ)
  pretty (SFuncRef (FuncRef i)) = "f" <> pretty i

instance Pretty Instruction where
  pretty (ICopy dest src) = pretty dest <+> ":=" <+> pretty src
  pretty (IIf cond thn els) = vsep
    [ "if" <+> pretty cond <+> "{"
    , indent 2 (vsep (map pretty thn))
    , "} else {"
    , indent 2 (vsep (map pretty els))
    , "}"
    ]
  pretty (ICall ret funcRef args) = 
    pretty ret <+> ":=" <+> pretty funcRef <> parens (hsep (punctuate "," (map pretty args)))
    where punctuate sep = foldr (\x acc -> if null acc then [x] else x <> sep : acc) []
  pretty (IBinOp op dest a b) = pretty dest <+> ":=" <+> pretty a <+> pretty op <+> pretty b
  pretty (IFor (Location counter) initial steps step body) = vsep
    [ "for var" <> pretty counter <+> "=" <+> pretty initial <+> "to" <+> pretty steps <+> "step" <+> pretty step <+> "{"
    , indent 2 (vsep (map pretty body))
    , "}"
    ]

instance Pretty ProgramFunc where
  pretty (ProgramFunc params locals instructions) = vsep
    [ "params:" <+> hsep (punctuate "," [ pretty ident <> ":" <> pretty region <> ":" <> pretty (showType typ) | (ident, region, typ) <- params ])
    , "locals:" <+> hsep (punctuate "," [ "var" <> pretty loc <> ":" <> pretty (showType typ) | (Location loc, typ) <- M.toList locals ])
    , "body:"
    , indent 2 (vsep (map pretty instructions))
    ]
    where punctuate sep = foldr (\x acc -> if null acc then [x] else x <> sep : acc) []

instance Pretty Program where
  pretty (Program globals funcMap tick startup ref) = vsep
    [ "globals:" <+> hsep (punctuate "," [ "var" <> pretty loc <> ":" <> pretty (showType typ) | (Location loc, typ) <- M.toList globals ])
    , ""
    , "functions:"
    , vsep [ "f" <> pretty i <> ":" <+> vsep [ "{",  indent 2 (pretty func), "}" ] | (FuncRef i, func) <- M.toList funcMap ]
    , ""
    , "startup:"
    , indent 2 (vsep (map pretty startup))
    , ""
    , "tick:"
    , indent 2 (vsep (map pretty tick))
    , ""
    , "result:" <+> pretty ref
    ]
    where punctuate sep = foldr (\x acc -> if null acc then [x] else x <> sep : acc) []
