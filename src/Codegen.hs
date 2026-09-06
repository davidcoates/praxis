-- | LLVM code generation: translates a lowered program to an LLVM module, and drives clang to build an executable.
--
-- The translation is local, relying on the guarantees of the 'Lower' stage: there is no polymorphism, every function
-- is top level, every variable is consumed exactly once on every path, and globals are read only.
module Codegen
  ( run
  , compile
  , printModule
  , Module
  ) where

import           Check.State         (instanceEnv)
import           Check.Type.Instance (isInstance)
import           Codegen.Builder
import           Codegen.Inbuilt
import           Codegen.IR          hiding (Switch)
import           Codegen.Layout
import           Codegen.Runtime     (runtimeSource)
import           Common
import           Introspect
import           Praxis              hiding (abort, fresh)
import           Stage
import           Term                hiding (Op)

import           Control.Monad       (forM, forM_)
import           Data.Char           (ord)
import           Data.Map.Strict     (Map)
import qualified Data.Map.Strict     as Map
import           Data.Maybe          (mapMaybe)
import           Prelude             hiding (null)
import           System.Exit         (ExitCode (..))
import           System.Process      (readProcessWithExitCode)


type Env = Map Name Operand

-- | Generate the LLVM module for a program.
run :: Annotated Lower Program -> Praxis Module
run program = do
  env <- use (checkState . instanceEnv)
  entry <- use mainName
  m <- runBuilder (genProgram entry program) (set isCopy (isInstance env Copy) emptyState)
  display Codegen "module" (printModule m) `ifFlag` debug
  return m

-- | Write the module and the runtime next to the output, then build the executable with clang (unless only the IR
-- is wanted).
compile :: Module -> FilePath -> Bool -> Praxis ()
compile m out emitOnly = do
  let ll = out ++ ".ll"
      c  = out ++ ".runtime.c"
  liftIOUnsafe $ do
    writeFile ll (printModule m)
    writeFile c runtimeSource
  unless emitOnly $ do
    (code, _, err) <- liftIOUnsafe $ readProcessWithExitCode "clang" ["-O2", "-Wno-override-module", ll, c, "-o", out] ""
    case code of
      ExitSuccess   -> return ()
      ExitFailure _ -> throw Codegen ("clang failed:\n" ++ err)


-- * Declarations

genProgram :: Maybe Name -> Annotated Lower Program -> Builder ()
genProgram entry (_ :< Program decls) = do
  let terms = concatMap declTerms decls
  mapM_ collectType decls
  mapM_ collectTerm terms
  mapM_ genTerm terms
  -- Globals are initialized in declaration order, before main.
  gs <- use globalVals
  defineExported "praxis_init" Void [] $ \[] -> do
    forM_ terms $ \(_ :< DeclTermVar name _ body) -> case Map.lookup name gs of
      Just (sym, _) -> do
        v <- genExp Map.empty body
        instr_ (Store v (global sym))
      Nothing -> return ()
    terminate RetVoid
  case entry of
    Nothing -> codegenError "missing main function"
    Just name -> do
      k <- lookupKnown name
      defineExported "praxis_main" Void [] $ \[] -> do
        _ <- callKnown k unitConst
        terminate RetVoid

declTerms :: Annotated Lower Decl -> [Annotated Lower DeclTerm]
declTerms (_ :< decl) = case decl of
  DeclTerm dt -> [dt]
  DeclRec ds  -> mapMaybe (\(_ :< d) -> case d of { DeclRecTerm dt -> Just dt; _ -> Nothing }) ds
  _           -> []

collectType :: Annotated Lower Decl -> Builder ()
collectType (_ :< decl) = case decl of
  DeclType dt -> collect dt
  DeclRec ds  -> forM_ ds $ \(_ :< d) -> case d of { DeclRecType dt -> collect dt; _ -> return () }
  _           -> return ()
  where
    collect (_ :< dt) = case dt of
      DeclTypeData mode name [] cons -> do
        let cons' = [ (con, payloadType qTy) | (_, qTy) :< DataCon con _ <- cons ]
        dataTypes %= Map.insert name (DataInfo mode cons')
        forM_ (zip [0..] cons') $ \(i, (con, _)) -> conInfos %= Map.insert con (ConInfo name i)
      DeclTypeData _ name _ _ -> codegenError ("polymorphic data type " ++ nameString name ++ " survived lowering")
      DeclTypeEnum name cons -> do
        enums %= Map.insert name cons
        forM_ (zip [0..] cons) $ \(i, con) -> enumCons %= Map.insert con (name, i)
      _ -> return ()
    payloadType qTy = case view value qTy of
      Mono (_ :< TypeFn arg _) -> arg
      _                        -> error "codegen: unexpected constructor type"

-- | A top-level declaration is a known function if its body is a function, and a global value otherwise.
collectTerm :: Annotated Lower DeclTerm -> Builder ()
collectTerm (_ :< DeclTermVar name _ body@((_, ty) :< exp)) = case exp of
  Lambda _ _ | (_ :< TypeFn arg ret) <- ty -> knownFns %= Map.insert name (Known (symbolOf name) arg ret)
  Cases _    | (_ :< TypeFn arg ret) <- ty -> knownFns %= Map.insert name (Known (symbolOf name) arg ret)
  _ -> do
    lt <- lowerType ty
    addGlobal (GlobalVar (symbolOf name) lt Zero False)
    globalVals %= Map.insert name (symbolOf name, ty)
collectTerm _ = return ()

genTerm :: Annotated Lower DeclTerm -> Builder ()
genTerm (_ :< DeclTermVar name _ ((_, ty) :< exp)) = do
  fns <- use knownFns
  case (Map.lookup name fns, exp) of
    (Just k, Lambda pat body) -> function k $ \arg -> do
      env <- bindIrrefutable Map.empty arg pat
      genExp env body
    (Just k, Cases alts) -> function k $ \arg -> genAlts Map.empty (knownRet k) arg alts
    _ -> return ()
  where
    function k body = do
      at <- lowerType (knownArg k)
      rt <- lowerType (knownRet k)
      defineFunction (knownSym k) rt [at] $ \[arg] -> do
        r <- body arg
        terminate (Ret r)
genTerm _ = return ()

lookupKnown :: Name -> Builder Known
lookupKnown name = use knownFns >>= \fns -> case Map.lookup name fns of
  Just k  -> return k
  Nothing -> codegenError ("unknown function " ++ nameString name)

callKnown :: Known -> Operand -> Builder Operand
callKnown k arg = do
  rt <- lowerType (knownRet k)
  instr rt (Call rt (global (knownSym k)) [arg])


-- * Expressions

genExp :: Env -> Annotated Lower Exp -> Builder Operand
genExp env ((_, ty) :< exp) = case exp of

  Var x -> case Map.lookup x env of
    Just v  -> return v
    Nothing -> do
      fns <- use knownFns
      gs <- use globalVals
      case (Map.lookup x fns, Map.lookup x gs) of
        (Just k, _) -> staticClosure k
        (_, Just (sym, gty)) -> do
          -- A use of a global is a read. For a Copy type the reference normalizes away, so the use is a copy.
          lt <- lowerType gty
          v <- instr lt (Load lt (global sym))
          if isRefType ty then return v else copyValue ty v
        _ -> codegenError ("unknown variable " ++ nameString x)

  Lit lit -> case lit of
    Integer n -> (\lt -> intConst lt n) <$> lowerType ty
    Bool b    -> return (boolConst b)
    Char c    -> return (intConst i32 (toInteger (ord c)))
    String s  -> if isRefType ty then stringLiteral s else heapString s

  Unit -> return unitConst

  Pair a b -> do
    x <- genExp env a
    y <- genExp env b
    pair x y

  Apply f arg -> genApply env ty f arg

  Closure caps (_ :< Var f) -> do
    k <- lookupKnown f
    vals <- forM caps $ \(name, qTy) -> case Map.lookup name env of
      Just v  -> return (captureType qTy, v)
      Nothing -> codegenError ("unknown captured variable " ++ nameString name)
    makeClosure k vals

  Closure _ _ -> codegenError "closure over a non-function"

  Con c -> do
    es <- use enumCons
    case Map.lookup c es of
      Just (_, i) -> return (intConst i32 (toInteger i))
      Nothing     -> conFunction c >>= staticClosure

  Inbuilt inbuilt -> inbuiltKnown inbuilt ty >>= staticClosure

  Specialize (_ :< Inbuilt inbuilt) _ -> inbuiltKnown inbuilt ty >>= staticClosure

  Specialize _ _ -> codegenError "specialization survived lowering"

  Case scrut alts -> do
    s <- genExp env scrut
    genAlts env ty s alts

  If cond thenExp elseExp -> do
    c <- genExp env cond
    thenL <- freshLabel "then"
    elseL <- freshLabel "else"
    joinL <- freshLabel "join"
    terminate (CondBr c thenL elseL)
    newBlock thenL
    t <- genExp env thenExp
    thenEnd <- currentBlock
    terminate (Br joinL)
    newBlock elseL
    e <- genExp env elseExp
    elseEnd <- currentBlock
    terminate (Br joinL)
    newBlock joinL
    rt <- lowerType ty
    instr rt (Phi rt [(t, thenEnd), (e, elseEnd)])

  Switch alts -> do
    joinL <- freshLabel "join"
    let go [] = abort "inexhaustive switch" >> return []
        go ((cond, body) : rest) = do
          c <- genExp env cond
          bodyL <- freshLabel "body"
          nextL <- freshLabel "next"
          terminate (CondBr c bodyL nextL)
          newBlock bodyL
          v <- genExp env body
          from <- currentBlock
          terminate (Br joinL)
          newBlock nextL
          ((v, from) :) <$> go rest
    incoming <- go alts
    newBlock joinL
    rt <- lowerType ty
    instr rt (Phi rt incoming)

  Let (_ :< Bind pat rhs) body -> do
    v <- genExp env rhs
    env' <- bindIrrefutable env v pat
    genExp env' body

  Read _ e -> genExp env e

  Defer a b -> do
    v <- genExp env a
    _ <- genExp env b
    return v

  Seq a b -> genExp env a >> genExp env b

  Sig e _ -> genExp env e

  Lambda _ _ -> codegenError "lambda survived lifting"

  Cases _ -> codegenError "cases survived lifting"

  _ -> codegenError "unexpected expression"

-- | Types carry no annotation in either stage, so they can be freely cast.
captureType :: Annotated Lower QType -> Type'
captureType (_ :< Mono t) = cast t where
  cast :: forall a. IsTerm a => Annotated Lower a -> Annotated TypeCheck a
  cast ((src, _) :< term) = case termT :: TermT a of
    TypeT -> (src, ()) :< runIdentity (recurseTerm (Identity . cast) term)
captureType _ = error "codegen: polymorphic capture"

pair :: Operand -> Operand -> Builder Operand
pair x@(Op tx _) y@(Op ty _) = do
  let t = Struct [tx, ty]
  p <- instr t (InsertValue (undef t) x [0])
  instr t (InsertValue p y [1])

genApply :: Env -> Type' -> Annotated Lower Exp -> Annotated Lower Exp -> Builder Operand
genApply env ty f@((_, fTy) :< fExp) arg = case fExp of

  Var g | not (Map.member g env) -> do
    fns <- use knownFns
    case Map.lookup g fns of
      Just k  -> genExp env arg >>= callKnown k
      Nothing -> indirect

  Con c -> do
    (ci, d, _) <- lookupCon c
    payload <- genExp env arg
    constructData d ci payload

  Inbuilt inbuilt -> do
    k <- inbuiltKnown inbuilt fTy
    genExp env arg >>= callKnown k

  Specialize (_ :< Inbuilt inbuilt) _ -> do
    k <- inbuiltKnown inbuilt fTy
    genExp env arg >>= callKnown k

  _ -> indirect

  where
    indirect = do
      c <- genExp env f
      a <- genExp env arg
      callClosure ty c a

-- | The function constructing a data value, for a constructor used as a value.
conFunction :: Name -> Builder Known
conFunction c = do
  (ci, d, payloadTy) <- lookupCon c
  let dataTy = phantom (TypeCon (conData ci))
      k = Known ("con " ++ symbolOf c) payloadTy dataTy
  fns <- use statics
  unless (Map.member (knownSym k) fns) $ do
    pt <- lowerType payloadTy
    dt <- lowerType dataTy
    defineFunction (knownSym k) dt [pt] $ \[payload] -> do
      v <- constructData d ci payload
      terminate (Ret v)
  return k


-- * Pattern matching

-- | Generate the alternatives of a case, returning the result.
genAlts :: Env -> Type' -> Operand -> [(Annotated Lower Pat, Annotated Lower Exp)] -> Builder Operand
genAlts env ty scrut alts = do
  joinL <- freshLabel "join"
  let go [] = abort "no matching pattern" >> return []
      go ((pat, body) : rest) = do
        nextL <- freshLabel "alt"
        (binds, frees) <- matchPat scrut pat False nextL
        mapM_ (\cell -> runtimeCall_ "praxis_free" [cell]) frees
        v <- genExp (binds <> env) body
        from <- currentBlock
        terminate (Br joinL)
        newBlock nextL
        ((v, from) :) <$> go rest
  incoming <- go alts
  newBlock joinL
  rt <- lowerType ty
  instr rt (Phi rt incoming)

-- | Bind a pattern which is expected to match (aborting if it does not).
bindIrrefutable :: Env -> Operand -> Annotated Lower Pat -> Builder Env
bindIrrefutable env v pat = do
  failL <- freshLabel "fail"
  (binds, frees) <- matchPat v pat False failL
  mapM_ (\cell -> runtimeCall_ "praxis_free" [cell]) frees
  when (refutable pat) $ do
    contL <- freshLabel "cont"
    terminate (Br contL)
    newBlock failL
    abort "no matching pattern"
    newBlock contL
  return (binds <> env)

refutable :: Annotated Lower Pat -> Bool
refutable (_ :< pat) = case pat of
  PatAt _ p   -> refutable p
  PatData _ _ -> True
  PatEnum _   -> True
  PatLit _    -> True
  PatPair p q -> refutable p || refutable q
  _           -> False

-- | Match a value against a pattern, branching to the failure label if it does not match. Returns the variables bound
-- and the (owned, boxed) cells to free once the match has succeeded.
--
-- A value matched through a reference is borrowed: its parts are not moved out, so any part bound at a non-reference
-- (hence Copy) type is copied.
matchPat :: Operand -> Annotated Lower Pat -> Bool -> String -> Builder (Env, [Operand])
matchPat v ((_, ty) :< pat) borrowed failL = case pat of

  PatVar x -> do
    v' <- if borrowed && not (isRefType ty) then copyValue ty v else return v
    return (Map.singleton x v', [])

  PatHole -> return (Map.empty, [])

  PatUnit -> return (Map.empty, [])

  PatAt x inner -> do
    (binds, frees) <- matchPat v inner borrowed failL
    -- The whole value is bound as well as its parts, so it is copied if the parts are moved out.
    v' <- if (borrowed && not (isRefType ty)) || not (Map.null binds) then copyValue ty v else return v
    return (Map.insert x v' binds, frees)

  PatLit lit -> do
    c <- case lit of
      Integer n -> let Op lt _ = v in instr i1 (ICmp "eq" v (intConst lt n))
      Bool b    -> instr i1 (ICmp "eq" v (boolConst b))
      Char ch   -> instr i1 (ICmp "eq" v (intConst i32 (toInteger (ord ch))))
      String _  -> codegenError "string patterns are not supported"
    test c
    return (Map.empty, [])

  PatEnum e -> do
    i <- lookupEnumCon e
    c <- instr i1 (ICmp "eq" v (intConst i32 (toInteger i)))
    test c
    return (Map.empty, [])

  PatPair p q -> do
    let Op (Struct [ta, tb]) _ = v
        borrowed' = borrowed || isRefType ty
    a <- instr ta (ExtractValue v [0])
    b <- instr tb (ExtractValue v [1])
    (binds1, frees1) <- matchPat a p borrowed' failL
    (binds2, frees2) <- matchPat b q borrowed' failL
    return (binds1 <> binds2, frees1 ++ frees2)

  PatData c inner -> do
    (ci, d, _) <- lookupCon c
    layout <- dataLayout d
    let Struct fields = layout
        borrowed' = borrowed || isRefType ty
        i = conTag ci
    tag <- case dataMode d of
      DataUnboxed -> instr i32 (ExtractValue v [0])
      DataBoxed   -> loadField layout v 0
    when (length (dataCons d) > 1) $ do
      ok <- instr i1 (ICmp "eq" tag (intConst i32 (toInteger i)))
      test ok
    payload <- case dataMode d of
      DataUnboxed -> instr (fields !! (i + 1)) (ExtractValue v [i + 1])
      DataBoxed   -> loadField layout v (i + 1)
    (binds, frees) <- matchPat payload inner borrowed' failL
    let owned = dataMode d == DataBoxed && not borrowed'
    return (binds, [ v | owned ] ++ frees)

  where
    test c = do
      okL <- freshLabel "match"
      terminate (CondBr c okL failL)
      newBlock okL
