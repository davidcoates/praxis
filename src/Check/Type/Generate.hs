{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}


module Check.Type.Generate
  ( run
  ) where

import           Check.Error
import           Check.Type.Reason
import           Check.Type.Require
import           Check.Type.System
import           Common
import           Env
import qualified Env.LEnv           as LEnv
import           Introspect
import           Praxis
import           Print
import           Stage
import           Term

import           Control.Monad      (replicateM)
import           Data.Foldable      (foldMap, foldlM)
import           Data.List          (nub, partition, sort)
import           Data.Maybe         (isJust, mapMaybe)
import           Data.Set           (Set)
import qualified Data.Set           as Set
import           Prelude            hiding (exp, log, lookup, read)
import qualified Prelude            (lookup)

ty :: (Term a, Functor f, Annotation a ~ Annotated Type) => (Annotated Type -> f (Annotated Type)) -> Annotated a -> f (Annotated a)
ty = annotation . just

mono :: Annotated Type -> Annotated QType
mono t = (view source t, Nothing) :< Forall [] [] t

specialise :: Source -> [Annotated QTyVar] -> [Annotated TyConstraint] -> Praxis (Annotated Type -> Annotated Type)
specialise s vs cs = do
  vars <- series $ [ (\t -> (n, view value t)) <$> freshTyUni | QTyVar n <- map (view value) vs ]
  opVars <- series $ [ (\t -> ((n, d), view value t)) <$> freshViewUni d | QViewVar d n <- map (view value) vs ]
  let f :: Term a => a -> Maybe a
      f x = case typeof x of
        IType |   TyVar n   <- x -> n `Prelude.lookup` vars
        IView | ViewVar d n <- x -> (n, d) `Prelude.lookup` opVars
        _                        -> Nothing
  requires [ newConstraint (view value (sub f c)) Specialisation s | c <- cs ]
  return (sub f)

specialiseQType :: Source -> Annotated QType -> Praxis (Annotated Type)
specialiseQType s (_ :< Forall vs cs t) = ($ t) <$> specialise s vs cs

join :: Praxis a -> Praxis b -> Praxis (a, b)
join f1 f2 = do
  l <- use tEnv
  x <- f1
  l1 <- use tEnv
  tEnv .= l
  y <- f2
  l2 <- use tEnv
  tEnv .= LEnv.join l1 l2
  return (x, y)

closure :: Praxis a -> Praxis a
closure x = scope (tEnv %= LEnv.capture >> x)

scope :: Praxis a -> Praxis a
scope x = save tEnv $ do
  x

read :: Source -> Name -> Praxis (Name, Annotated Type)
read s n = do
  l <- use tEnv
  r@(_ :< ViewRef refName) <- freshViewRef
  case LEnv.lookupFull n l of
    Just entry -> do
      t <- specialiseQType s (view LEnv.value entry)
      requires [ newConstraint (Share t) (UnsafeRead n) s | view LEnv.used entry ]
      requires [ newConstraint (Share t) (Captured n) s   | view LEnv.captured entry  ]
      return $ (refName, phantom (TyApply (phantom (View r)) t))
    Nothing -> throwAt s (NotInScope n)

-- |Marks a variable as used, and generate a Share constraint if it has already been used.
mark :: Source -> Name -> Praxis (Annotated Type)
mark s n = do
  l <- use tEnv
  case LEnv.lookupFull n l of
    Just entry -> do
      t <- specialiseQType s (view LEnv.value entry)
      tEnv %= LEnv.mark n
      requires [ newConstraint (Share t) (MultiUse n) s | view LEnv.used entry ]
      requires [ newConstraint (Share t) (Captured n) s | view LEnv.captured entry ]
      return t
    Nothing -> throwAt s (NotInScope n)

introTy :: Source -> Name -> Annotated QType -> Praxis ()
introTy s n t = do
  l <- use tEnv
  case lookup n l of
    Just _ -> throwAt s $ "variable " <> quote (pretty n) <> " redeclared"
    _      -> tEnv %= intro n t

getType :: Source -> Name -> Praxis (Annotated QType)
getType s n = do
  l <- use tEnv
  case lookup n l of
    Just t  -> return t
    Nothing -> throwAt s (NotInScope n)

getData :: Source -> Name -> Praxis DataConInfo
getData s n = do
  l <- use daEnv
  case lookup n l of
    Just v  -> return (view (annotation . just) v)
    Nothing -> throwAt s $ "data constructor " <> quote (pretty n) <> " is not in scope"

run :: Term a => Annotated a -> Praxis (Annotated a)
run term = save stage $ do
  stage .= TypeCheck Generate
  term <- generate term
  display term `ifFlag` debug
  cs <- use (our . constraints)
  (`ifFlag` debug) $ do
    display (separate "\n\n" (nub . sort $ cs))
    use tEnv >>= display
    use daEnv >>= display
  return term

generate :: forall a. Term a => Annotated a -> Praxis (Annotated a)
generate term = ($ term) $ case witness :: I a of
  IExp     -> generateExp
  IBind    -> generateBind
  IDataCon -> error "standalone DataCon"
  IDecl    -> generateDecl Nothing
  IPat     -> error "standalone Pat"
  _        -> value (recurse generate)

-- Computes in 'parallel' (c.f. `sequence` which computes in series)
-- For our purposes we require each 'branch' to start with the same type environment TODO kEnv etc
-- The output environments are all contextJoined
parallel :: [Praxis a] -> Praxis [a]
parallel []     = return []
parallel [x]    = (:[]) <$> x
parallel (x:xs) = do
  (a, as) <- join x (parallel xs)
  return (a:as)

-- TODO move this somewhere
fun :: Annotated Type -> Annotated Type -> Annotated Type
fun a b = TyFun a b `as` phantom KindType

equal :: Annotated Type -> Annotated Type -> Reason -> Source -> Praxis ()
equal t1 t2 r s = require $ newConstraint (t1 `TEq` t2) r s

-- TODO use introspection?
patToTy :: Annotated TyPat -> Annotated Type
patToTy = over value patToTy' where
  patToTy' = \case
    TyPatVar n       -> TyVar n
    TyPatViewVar d n -> View (phantom (ViewVar d n))
    TyPatPack a b    -> TyPack (patToTy a) (patToTy b)

unis :: Annotated TyPat -> Set (Annotated QTyVar)
unis = extract (embedMonoid f) where
  f = \case
    TyPatVar n       -> Set.singleton (phantom $ QTyVar n)
    TyPatViewVar d n -> Set.singleton (phantom $ QViewVar d n)
    _                -> Set.empty

generateDataCon :: [Annotated QTyVar] -> Annotated Type -> Annotated DataCon -> Praxis (Annotated DataCon)
generateDataCon vars retType ((src, Nothing) :< DataCon name argType) = do
  let fullType = phantom $ Forall vars [] $ case argType of -- Type of the constructor -- FIXME constraints???
        Just argType -> fun argType retType
        Nothing      -> retType
      dataCon = ((src, Just (DataConInfo {fullType, argType, retType})) :< DataCon name argType)
  daEnv %= Env.intro name dataCon
  return dataCon


generateDecl :: Maybe (Annotated QType) -> Annotated Decl -> Praxis (Annotated Decl)
generateDecl forwardT = splitTrivial $ \src -> \case

  -- TODO Share constraints needed!
  DeclData name arg alts -> do
    -- TODO could be kind annotated to avoid this lookup
    Just k <- kEnv `uses` Env.lookup name

    -- The return type of the constructors
    let returnTy = case arg of
          Nothing -> TyCon name `as` k
          Just arg
            | KindFun k1 k2 <- view value k -> TyApply (TyCon name `as` k) (patToTy arg) `as` k2

        vars = Set.toList (foldMap unis arg)

    alts <- traverse (generateDataCon vars returnTy) alts
    return $ DeclData name arg alts

  op@(DeclOp _ _ _) -> return op

  DeclRec decls -> do

    terms <- mapM preDeclare decls
    decls <- mapM (\(ty, decl) -> generateDecl (Just ty) decl) terms
    return $ DeclRec decls
    where
      getTyFromSig = \case
        Nothing -> mono <$> freshTyUni
        Just ty -> pure ty
      preDeclare decl = case decl of
        ((src, _) :< DeclTerm name sig exp)
          | expIsRecSafe exp -> do { ty <- getTyFromSig sig; introTy src name ty; return (ty, decl) }
          | otherwise        -> throwAt src $ "non-function " <> quote (pretty name) <> " can not be recursive"
        _                    -> throwAt src ("illegal non-term in recursive block" :: String)


  DeclSyn name t -> return $ DeclSyn name t

  DeclTerm name sig exp -> do

    case sig of

      Nothing -> do
        exp <- generateExp exp
        case forwardT of
          Just (_ :< Forall [] [] t) -> equal t (view ty exp) (FunCongruence name) src
          Nothing                    -> introTy src name (mono (view ty exp))
        return $ DeclTerm name Nothing exp

      Just sig@(_ :< Forall boundVars cosntraints t) -> do
        our . axioms %= (++ [ axiom (view value c) | c <- cosntraints ]) -- Constraints in the signature are added as axioms
        exp <- generateExp exp
        case forwardT of
          Just _  -> return () -- forwardT is sig, so a FunCongruence constraint is redundant (covered by the below FunSignature constraint)
          Nothing -> introTy src name sig
        equal t (view ty exp) (FunSignature name) src
        return $ DeclTerm name (Just sig) exp


generateExp :: Annotated Exp -> Praxis (Annotated Exp)
generateExp = split $ \src -> \case

  Apply f x -> do
    rTy <- freshTyUni
    f <- generateExp f
    x <- generateExp x
    let fTy = view ty f
    let xTy = view ty x
    require $ newConstraint (fTy `TEq` fun xTy rTy) FunApplication src
    return (rTy :< Apply f x)

  Case exp alts -> do
    exp <- generateExp exp
    let expTy = view ty exp
    op <- freshViewUni RefOrValue
    alts <- parallel (map (generateAlt op) alts)
    ty1 <- equals (map fst alts) CaseCongruence
    ty2 <- equals (map snd alts) CaseCongruence
    equal expTy ty1 CaseCongruence src -- TODO probably should pick a better name for this
    return (ty2 :< Case exp alts)

  Cases alts -> closure $ do
    op <- freshViewUni RefOrValue
    alts <- parallel (map (generateAlt op) alts)
    ty1 <- equals (map fst alts) CaseCongruence
    ty2 <- equals (map snd alts) CaseCongruence
    return (fun ty1 ty2 :< Cases alts)

  Con name -> do
    DataConInfo { fullType } <- getData src name
    t <- specialiseQType src fullType
    return (t :< Con name)

  Do stmts -> scope $ do
    stmts <- traverse generate stmts
    case view value (last stmts) of
      StmtExp ((_, Just t) :< _) -> return (t :< Do stmts)
      _                          -> throwAt src ("do block must end in an expression" :: String)

  If condExp thenExp elseExp -> do
    condExp <- generateExp condExp
    (thenExp, elseExp) <- join (generateExp thenExp) (generateExp elseExp)
    require $ newConstraint (view ty condExp `TEq` TyCon "Bool" `as` phantom KindType) IfCondition src
    require $ newConstraint (view ty thenExp `TEq` view ty elseExp) IfCongruence src
    return (view ty thenExp :< If condExp thenExp elseExp)

  Lambda pat exp -> closure $ do
    op <- freshViewUni RefOrValue
    (pat, exp) <- generateAlt op (pat, exp)
    return (fun (view ty pat) (view ty exp) :< Lambda pat exp)

  Let bind exp -> scope $ do
    bind <- generateBind bind
    exp <- generateExp exp
    return (view ty exp :< Let bind exp)

  -- TODO pull from environment?
  Lit lit -> ((\t -> t `as` phantom KindType :< Lit lit) <$>) $ case lit of
    Int  _   -> return $ TyCon "Int"
    Bool _   -> return $ TyCon "Bool"
    Char _   -> return $ TyCon "Char"
    String _ -> do
      op <- freshViewUni RefOrValue
      let arr = TyCon "Array" `as` phantom (KindFun (phantom KindType) (phantom KindType))
          str = TyApply arr (TyCon "Char" `as` phantom KindType) `as` phantom KindType
      return $ TyApply (View op `as` phantom KindView) str

  Read var exp -> scope $ do
    (refName, t) <- read src var
    tEnv %= LEnv.adjust (const (mono t)) var
    exp <- generateExp exp
    require $ newConstraint (RefFree refName (view ty exp)) SafeRead src
    return (view ty exp :< view value exp)

  Pair exp1 exp2 -> do
    exp1 <- generateExp exp1
    exp2 <- generateExp exp2
    let t = TyPair (view ty exp1) (view ty exp2) `as` phantom KindType
    return (t :< Pair exp1 exp2)

  Sig exp t -> do
    exp <- generateExp exp
    equal t (view ty exp) UserSignature src
    return (t :< Sig exp t)

  Switch alts -> do
    constraints <- sequence (map (generateExp . fst) alts)
    requires [ newConstraint (view ty c `TEq` TyCon "Bool" `as` phantom KindType) SwitchCondition (view source c) | c <- constraints]
    exps <- parallel (map (generateExp . snd) alts)
    t <- equals exps SwitchCongruence
    return (t :< Switch (zip constraints exps))

  Unit -> do
    let t = TyUnit `as` phantom KindType
    return (t :< Unit)

  Var name -> do
    t <- mark src name
    return (t :< Var name)

  Where exp decls -> scope $ do
    decls <- traverse (generateDecl Nothing) decls
    exp <- generateExp exp
    return (view ty exp :< Where exp decls)


equals :: (Term a, Annotation a ~ Annotated Type) => [Annotated a] -> Reason -> Praxis (Annotated Type)
equals es = equals' (map (\e -> (view source e, view ty e)) es) where
  equals' :: [(Source, Annotated Type)] -> Reason -> Praxis (Annotated Type)
  equals' ((_, t):ts) r = sequence [equal t t' r s | (s, t') <- ts] >> return t


generateBind :: Annotated Bind -> Praxis (Annotated Bind)
generateBind = splitTrivial $ \src -> \case

  Bind pat exp -> do
    exp <- generateExp exp
    op <- freshViewUni RefOrValue
    pat <- generatePat op pat
    equal (view ty pat) (view ty exp) (BindCongruence) (view source pat <> view source exp)
    return $ Bind pat exp


generateAlt :: Annotated View -> (Annotated Pat, Annotated Exp) -> Praxis (Annotated Pat, Annotated Exp)
generateAlt op (pat, exp) = scope $ do
  pat <- generatePat op pat
  exp <- generateExp exp
  return (pat, exp)


generatePat :: Annotated View -> Annotated Pat -> Praxis (Annotated Pat)
generatePat op pat = snd <$> generatePat' pat where

  wrap t = TyApply (View op `as` phantom KindView) t `as` phantom KindType

  generatePat' :: Annotated Pat -> Praxis (Annotated Type, Annotated Pat)
  generatePat' = splitPair $ \src -> \case

    PatAt name pat -> do
      (t, pat) <- generatePat' pat
      introTy src name (mono t)
      require $ newConstraint (Share t) (MultiAlias name) src
      return (t, wrap t :< PatAt name pat)

    PatCon name pat -> do
      -- Lookup the data alternative with this name
      DataConInfo { fullType, argType, retType } <- getData src name
      when (isJust argType /= isJust pat) $ throwAt src $ "wrong number of arguments applied to data constructor " <> quote (pretty name)

      let Forall boundVars constraints _ = view value fullType
      f <- specialise src boundVars constraints
      let retType' = f retType

      case pat of
        Nothing -> return (retType', wrap retType' :< PatCon name Nothing)
        Just pat -> do
          (patArgType, pat) <- generatePat' pat
          let Just argType' = argType
          require $ newConstraint (patArgType `TEq` f argType') (ConPattern name) src
          return (retType', wrap retType' :< PatCon name (Just pat))

    PatHole -> do
      t <- freshTyUni
      return (t, wrap t :< PatHole)

    -- TODO think about how view literals would work, e.g. x@"abc"
    PatLit lit -> let t = TyCon (litName lit) `as` phantom KindType in return (t, t :< PatLit lit) where
      litName = \case
        Bool _   -> "Bool"
        Char _   -> "Char"
        Int _    -> "Int"
        String _ -> "String"

    PatPair pat1 pat2 -> do
      (t1, pat1) <- generatePat' pat1
      (t2, pat2) <- generatePat' pat2
      let t = TyPair t1 t2 `as` phantom KindType
      return (t, wrap t :< PatPair pat1 pat2)

    PatUnit -> do
      let t = TyUnit `as` phantom KindType
      return (t, t :< PatUnit)

    PatVar var -> do
      t <- freshTyUni
      introTy src var (mono (wrap t))
      return (t, wrap t :< PatVar var)
