module LambdaLift
  ( run
  , runExp
  ) where

import           Common
import           Introspect
import           Praxis
import           Stage
import           Term

import           Control.Monad       (foldM, forM_)
import           Control.Monad.Trans (lift)
import           Data.Map.Strict     (Map)
import qualified Data.Map.Strict     as Map
import           Data.Maybe          (fromMaybe)
import           Data.Set            (Set)
import qualified Data.Set            as Set

import           Control.Monad.State (StateT, modify, runStateT)


-- | StateT accumulates top-level lifted declarations.
type LiftM = StateT [Annotated Monomorphize Decl] Praxis


-- * Entry points

run :: Annotated Monomorphize Program -> Praxis (Annotated Monomorphize Program)
run prog = do
  (prog', lifted) <- runStateT (liftProgram prog) []
  let (_ :< Program decls) = prog'
      result = phantom (Program (lifted ++ decls))
  display LambdaLift "lambda lifted program" result `ifFlag` debug
  return result

runExp :: Annotated Monomorphize Program -> Annotated Monomorphize Exp -> Praxis (Annotated Monomorphize Program, Annotated Monomorphize Exp)
runExp prog exp = do
  (prog', liftedProg) <- runStateT (liftProgram prog) []
  let (_ :< Program decls) = prog'
      globals = Set.fromList
        [ name
        | (_ :< decl) <- decls
        , name <- case decl of
            DeclTerm (_ :< DeclTermVar name _ _) -> [name]
            DeclRec ds -> [ n | (_ :< DeclRecTerm (_ :< DeclTermVar n _ _)) <- ds ]
            _ -> []
        ]
  (exp', liftedExp) <- runStateT (liftExp globals exp) []
  let result = phantom (Program (liftedProg ++ liftedExp ++ decls))
  display LambdaLift "lambda lifted program" result `ifFlag` debug
  display LambdaLift   "lambda lifted exp"     exp'   `ifFlag` debug
  return (result, exp')


-- * Program-level lifting

liftProgram :: Annotated Monomorphize Program -> LiftM (Annotated Monomorphize Program)
liftProgram (_ :< Program decls) = do
  -- Collect all top-level names as globals so they're never treated as captures
  let globals = Set.fromList
        [ name
        | (_ :< decl) <- decls
        , name <- case decl of
            DeclTerm (_ :< DeclTermVar name _ _) -> [name]
            DeclRec ds -> [ n | (_ :< DeclRecTerm (_ :< DeclTermVar n _ _)) <- ds ]
            _ -> []
        ]
  decls' <- mapM (liftTopDecl globals) decls
  return (phantom (Program decls'))

liftTopDecl :: Set Name -> Annotated Monomorphize Decl -> LiftM (Annotated Monomorphize Decl)
liftTopDecl globals (_ :< decl) = case decl of
  DeclTerm dt -> phantom . DeclTerm <$> liftTopDeclTerm globals dt
  DeclRec ds  -> phantom . DeclRec  <$> mapM (liftTopDeclRec globals) ds
  _           -> return (phantom decl)

liftTopDeclRec :: Set Name -> Annotated Monomorphize DeclRec -> LiftM (Annotated Monomorphize DeclRec)
liftTopDeclRec globals (_ :< dr) = case dr of
  DeclRecTerm dt  -> phantom . DeclRecTerm <$> liftTopDeclTerm globals dt
  DeclRecType dty -> return (phantom (DeclRecType dty))

liftTopDeclTerm :: Set Name -> Annotated Monomorphize DeclTerm -> LiftM (Annotated Monomorphize DeclTerm)
liftTopDeclTerm globals (_ :< DeclTermVar name qTy body) = do
  body' <- liftExp globals body
  return (phantom (DeclTermVar name qTy body'))
liftTopDeclTerm _ dt = return dt


-- * Expression-level lifting

liftExp :: Set Name -> Annotated Monomorphize Exp -> LiftM (Annotated Monomorphize Exp)
liftExp globals ((src, ty) :< exp) = case exp of

  Where body decls -> do
    (body', decls') <- liftWhere globals body decls
    case decls' of
      [] -> return body'
      _  -> return ((src, ty) :< Where body' decls')

  -- Recompute captures after lifting inner expression
  Closure _caps inner -> do
    inner' <- liftExp globals inner
    let caps = [ (n, phantom (Mono (phantom TypeUnit))) | (n, _) <- computeCaps globals inner' ]
    return ((src, ty) :< Closure caps inner')

  Let ((lsrc, lann) :< Bind pat rhs) body -> do
    rhs'  <- liftExp globals rhs
    body' <- liftExp globals body
    return ((src, ty) :< Let ((lsrc, lann) :< Bind pat rhs') body')

  Case scrut alts -> do
    scrut' <- liftExp globals scrut
    alts'  <- mapM (\(pat, e) -> (pat,) <$> liftExp globals e) alts
    return ((src, ty) :< Case scrut' alts')

  Cases alts -> do
    alts' <- mapM (\(pat, e) -> (pat,) <$> liftExp globals e) alts
    return ((src, ty) :< Cases alts')

  _ -> ((src, ty) :<) <$> recurseTerm liftChild exp
  where
    liftChild :: forall a. IsTerm a => Annotated Monomorphize a -> LiftM (Annotated Monomorphize a)
    liftChild child = case typeof (view value child) of
      ExpT -> liftExp globals child
      _    -> return child


-- * Where-expression lifting

-- | Process a Where expression's declarations:
-- - Function definitions (Closure bodies) are lifted to top-level
-- - Value bindings remain as Where decls (or become Let bindings)
-- Returns the rewritten body and remaining non-lifted decls.
liftWhere :: Set Name -> Annotated Monomorphize Exp -> [Annotated Monomorphize DeclTerm] -> LiftM (Annotated Monomorphize Exp, [Annotated Monomorphize DeclTerm])
liftWhere globals body decls = do
  -- Process decls left-to-right, accumulating rewrites and lifted globals
  (rewrites, extraGlobals) <- foldM (processDeclTerm globals) (Map.empty, Set.empty) decls
  let allGlobals = globals <> extraGlobals
      liftedNames = Map.keysSet rewrites
      letDecls = [ dt | dt@(_ :< DeclTermVar name _ _) <- decls, name `Set.notMember` liftedNames ]
  body'     <- liftExp allGlobals (applyRewrites rewrites body)
  letDecls' <- mapM (\dt -> liftDeclTermBody allGlobals (applyRewritesInDeclTerm rewrites dt)) letDecls
  return (body', letDecls')

liftDeclTermBody :: Set Name -> Annotated Monomorphize DeclTerm -> LiftM (Annotated Monomorphize DeclTerm)
liftDeclTermBody globals (_ :< DeclTermVar name qTy body) = do
  body' <- liftExp globals body
  return (phantom (DeclTermVar name qTy body'))
liftDeclTermBody _ dt = return dt

-- | Process one DeclTerm from a Where clause.
-- Accumulator: (rewrites, extraGlobals)
processDeclTerm
  :: Set Name    -- outer globals
  -> (Map Name (Annotated Monomorphize Exp), Set Name)
  -> Annotated Monomorphize DeclTerm
  -> LiftM (Map Name (Annotated Monomorphize Exp), Set Name)
processDeclTerm globals (rewrites, extraGlobals) dt =
  case view value dt of
    DeclTermVar name qTy body -> do
      let body' = applyRewrites rewrites body
          allGlobals = globals <> extraGlobals
      case view value body' of
        -- Function body: Closure wrapping a Lambda (or Cases) — lift to top level.
        -- Recompute caps using allGlobals so that previously-lifted names are excluded.
        Closure _stale inner -> do
          let caps = computeCaps allGlobals inner
          liftedName <- lift (freshVar name)
          let origType = view annotation body'
          case caps of
            [] -> do
              -- No captures: lift as a plain closed global
              let liftedBody = (Phantom, origType) :< Closure [] inner
                  liftedDecl = phantom (DeclTerm (phantom (DeclTermVar liftedName qTy liftedBody)))
                  callSite   = (Phantom, origType) :< Var liftedName
              modify (++ [liftedDecl])
              return (Map.insert name callSite rewrites, Set.insert liftedName extraGlobals)
            _ -> do
              -- Has captures: lift with capture tuple as extra parameter.
              -- Compute the new type: capsType -> origType.
              let capsType   = buildCapsType caps
                  newType    = phantom (TypeFn capsType origType)
                  newQTy     = fmap (\_ -> phantom (Mono (castType newType))) qTy
                  capsParam  = buildCapsPat caps
                  liftedBody = (Phantom, newType) :< Closure [] ((Phantom, newType) :< Lambda capsParam inner)
                  liftedDecl = phantom (DeclTerm (phantom (DeclTermVar liftedName newQTy liftedBody)))
                  capsArg    = buildCapsTuple caps
                  callSite   = (Phantom, origType) :< Apply ((Phantom, newType) :< Var liftedName) capsArg
              modify (++ [liftedDecl])
              return (Map.insert name callSite rewrites, Set.insert liftedName extraGlobals)
        -- Value binding: not lifted, excluded from rewrites
        _ -> return (rewrites, extraGlobals)
    _ -> return (rewrites, extraGlobals)


-- * Type casting

-- | Strip the TypeCheck annotation from a type, producing a Monomorphize-stage type.
-- Safe because Annotation Monomorphize Type = () = Annotation TypeCheck Type.
castType :: Annotated TypeCheck Type -> Annotated Monomorphize Type
castType (_ :< ty) = phantom $ case ty of
  TypeApply f x   -> TypeApply (castType f) (castType x)
  TypeApplyOp f x -> TypeApplyOp (castType f) (castType x)
  TypeCon n       -> TypeCon n
  TypeFn a b      -> TypeFn (castType a) (castType b)
  TypeIdentityOp  -> TypeIdentityOp
  TypePair a b    -> TypePair (castType a) (castType b)
  TypeRef n       -> TypeRef n
  TypeSetOp ts    -> TypeSetOp (Set.map castType ts)
  TypeUni f n     -> TypeUni f n
  TypeUnit        -> TypeUnit
  TypeVar f n     -> TypeVar f n


-- * Free variable analysis

-- | Collect free variables with their types.
-- When the same variable appears multiple times, the type from any occurrence is fine (they're all the same).
freeVarsWithTypes :: Set Name -> Set Name -> Annotated Monomorphize Exp -> Map Name (Annotated TypeCheck Type)
freeVarsWithTypes globals bound ((_, ty) :< exp) = case exp of
  Var name
    | name `Set.member` globals -> Map.empty
    | name `Set.member` bound   -> Map.empty
    | otherwise                 -> Map.singleton name ty
  Lambda pat inner ->
    freeVarsWithTypes globals (bound <> patNames pat) inner
  Let (_ :< Bind pat rhs) inner ->
    freeVarsWithTypes globals bound rhs <>
    freeVarsWithTypes globals (bound <> patNames pat) inner
  Closure _caps inner ->
    freeVarsWithTypes globals bound inner
  Where body decls ->
    let declNames = Set.fromList [ name | (_ :< DeclTermVar name _ _) <- decls ]
        bound'    = bound <> declNames
    in  freeVarsWithTypes globals bound' body <>
        foldMap (\dt -> case view value dt of
          DeclTermVar _ _ rhs -> freeVarsWithTypes globals bound rhs
          _                   -> Map.empty) decls
  Case scrut alts ->
    freeVarsWithTypes globals bound scrut <>
    foldMap (\(pat, e) -> freeVarsWithTypes globals (bound <> patNames pat) e) alts
  Cases alts ->
    foldMap (\(pat, e) -> freeVarsWithTypes globals (bound <> patNames pat) e) alts
  _ -> getConst $ recurseTerm (\child -> case typeof (view value child) of
        ExpT -> Const (freeVarsWithTypes globals bound child)
        _    -> Const Map.empty) exp

patNames :: Annotated Monomorphize Pat -> Set Name
patNames (_ :< pat) = case pat of
  PatAt name inner -> Set.insert name (patNames inner)
  PatData _ inner  -> patNames inner
  PatPair l r      -> patNames l <> patNames r
  PatVar name      -> Set.singleton name
  _                -> Set.empty

-- | Compute capture list for a Closure: all free vars in inner that are not global, with their types.
computeCaps :: Set Name -> Annotated Monomorphize Exp -> [(Name, Annotated TypeCheck Type)]
computeCaps globals inner =
  Map.toAscList (freeVarsWithTypes globals Set.empty inner)


-- * Capture tuple helpers

typeUnit :: Annotated TypeCheck Type
typeUnit = phantom TypeUnit

buildCapsType :: [(Name, Annotated TypeCheck Type)] -> Annotated TypeCheck Type
buildCapsType []             = typeUnit
buildCapsType [(_, ty)]      = ty
buildCapsType ((_, ty):rest) = phantom (TypePair ty (buildCapsType rest))

buildCapsPat :: [(Name, Annotated TypeCheck Type)] -> Annotated Monomorphize Pat
buildCapsPat []             = (Phantom, typeUnit) :< PatUnit
buildCapsPat [(n, ty)]      = (Phantom, ty) :< PatVar n
buildCapsPat ((n, ty):rest) = (Phantom, phantom (TypePair ty (buildCapsType rest))) :< PatPair ((Phantom, ty) :< PatVar n) (buildCapsPat rest)

buildCapsTuple :: [(Name, Annotated TypeCheck Type)] -> Annotated Monomorphize Exp
buildCapsTuple []             = (Phantom, typeUnit) :< Unit
buildCapsTuple [(n, ty)]      = (Phantom, ty) :< Var n
buildCapsTuple ((n, ty):rest) = (Phantom, phantom (TypePair ty (buildCapsType rest))) :< Pair ((Phantom, ty) :< Var n) (buildCapsTuple rest)


-- * Rewrite application

-- | Substitute variables according to a rewrite map.
-- Cannot use sub/embedSub since recurse fails at Monomorphize stage for Exp/Pat.
applyRewrites :: Map Name (Annotated Monomorphize Exp) -> Annotated Monomorphize Exp -> Annotated Monomorphize Exp
applyRewrites rewrites = rewriteExp
  where
    rewriteExp ann@((src, ty) :< exp) = case exp of
      Var name -> fromMaybe ann (Map.lookup name rewrites)
      _        -> (src, ty) :< runIdentity (recurseTerm rewriteAny exp)

    rewriteAny :: forall a. IsTerm a => Annotated Monomorphize a -> Identity (Annotated Monomorphize a)
    rewriteAny term = case typeof (view value term) of
      ExpT -> Identity (rewriteExp term)
      _    -> value (recurseTerm rewriteAny) term

applyRewritesInDeclTerm :: Map Name (Annotated Monomorphize Exp) -> Annotated Monomorphize DeclTerm -> Annotated Monomorphize DeclTerm
applyRewritesInDeclTerm rewrites (_ :< DeclTermVar name qTy body) =
  phantom (DeclTermVar name qTy (applyRewrites rewrites body))
applyRewritesInDeclTerm _ dt = dt
