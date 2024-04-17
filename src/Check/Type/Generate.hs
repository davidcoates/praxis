{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}


module Check.Type.Generate
  ( run
  ) where

import           Check.Error
import           Check.Type.Reason
import           Common
import           Env.Env           (Env (..))
import qualified Env.Env           as Env
import qualified Env.LEnv          as LEnv
import           Introspect
import           Praxis
import           Print
import           Stage
import           Term

import           Control.Monad     (replicateM)
import           Data.Foldable     (foldMap, foldlM)
import           Data.List         (nub, partition, sort)
import           Data.Maybe        (isJust, mapMaybe)
import qualified Data.Set          as Set
import           Prelude           hiding (log)


require :: Tag (Source, Reason) TyConstraint -> Praxis ()
require ((src, reason) :< con) = tySystem . requirements %= (((src, Just reason) :< Requirement con):)

requires :: [Tag (Source, Reason) TyConstraint] -> Praxis ()
requires = mapM_ require

ty :: (Term a, Functor f, Annotation a ~ Annotated Type) => (Annotated Type -> f (Annotated Type)) -> Annotated a -> f (Annotated a)
ty = annotation . just

mono :: Annotated Type -> Annotated QType
mono t = (view source t, Nothing) :< Forall [] [] t

specialiseQTyVar :: Annotated QTyVar -> Praxis (Name, Annotated Type)
specialiseQTyVar (a :< qTyVar) = case qTyVar of
  QTyVar n     -> (\t -> (n, a :< view value t)) <$> freshTyUni
  QViewVar d n -> (\t -> (n, a :< view value t)) <$> freshTyViewUni d

specialise :: Source -> Name -> [Annotated QTyVar] -> [Annotated TyConstraint] -> Praxis (Annotated Type -> Annotated Type, Specialisation)
specialise src name vars cs = do
  -- Note: TyVar and TyView-Var names are disjoint (regardless of view domains)
  specialisedVars <- mapM specialiseQTyVar vars
  let tyRewrite :: Term a => Annotated a -> Annotated a
      tyRewrite = sub (embedSub f)
      f :: Annotated Type -> Maybe (Annotated Type)
      f (_ :< t) = case t of
        TyVar n                   -> n `lookup` specialisedVars
        TyView (_ :< ViewVar _ n) -> n `lookup` specialisedVars
        _                         -> Nothing
  let specialisation = zip  vars (map snd specialisedVars)
  requires [ (src, Specialisation name) :< view value (tyRewrite c) | c <- cs ]
  return (tyRewrite, specialisation)

specialiseQType :: Source -> Name -> Annotated QType -> Praxis (Annotated Type, Specialisation)
specialiseQType s n (_ :< Forall vs cs t) = do
  (tyRewrite, specialisation) <- specialise s n vs cs
  let t' = tyRewrite t
  -- Require polymorphic terms to be copyable.
  --
  -- This will give the compiler the freedom to allocate just once per (type-distinct) specialisation
  -- instead of at every call site.
  --
  -- Ideally this check would happen at the definition of the polymorphic term, but that's not so easy.
  when (not (null vs)) $ require $ (s, Specialisation n) :< Copy t'
  return (t', specialisation)

join :: Source -> Praxis a -> Praxis b -> Praxis (a, b)
join src f1 f2 = do
  l <- use tEnv
  x <- f1
  l1 <- use tEnv
  tEnv .= l
  y <- f2
  l2 <- use tEnv
  tEnv .= LEnv.join l1 l2
  return (x, y)

closure :: Source -> Praxis a -> Praxis a
closure src x = do
  l1 <- use tEnv
  tEnv %= LEnv.setCaptured
  a <- scope src x
  l2 <- use tEnv
  -- Restore captured bit but save used bit
  tEnv .= Env.zipWith (\e1 e2 -> set LEnv.captured (view LEnv.captured e1) e2) l1 l2 -- This is disgusting
  return a

scope :: Source -> Praxis a -> Praxis a
scope src x = do
  Env l1 <- use tEnv
  a <- x
  Env l2 <- use tEnv
  let n = length l2 - length l1
      (newVars, oldVars) = splitAt n l2
      unusedVars = [ (n, view LEnv.value e) | (n, e) <- newVars, not (view LEnv.used e) && not (view LEnv.read e) ]
  series $ [ throwAt src (Unused n) | (n, _) <- unusedVars, head n /= '_' ] -- hacky
  tEnv .= Env oldVars
  return a

-- | Marks a variable as read, returning the view-type of the variable and the view ref-name.
-- A Copy constraint will be generated if the variable has already been used or has been captured.
readVar :: Source -> Name -> Praxis (Name, Annotated Type, Specialisation)
readVar src name = do
  l <- use tEnv
  r@(_ :< ViewRef refName) <- freshViewRef
  case Env.lookup name l of
    Just entry -> do
      (t, specialisation) <- specialiseQType src name (view LEnv.value entry)
      tEnv %= LEnv.setRead name
      requires [ (src, UnsafeRead name) :< Copy t | view LEnv.used entry ]
      requires [ (src,   Captured name) :< Copy t | view LEnv.captured entry ]
      return $ (refName, phantom (TyApply (phantom (TyView r)) t), specialisation)
    Nothing -> throwAt src (NotInScope name)

-- | Marks a variable as used, returning the type of the variable.
-- A Copy constraint will be generated if the variable has already been used or has been captured.
useVar :: Source -> Name -> Praxis (Annotated Type, Specialisation)
useVar src name = do
  l <- use tEnv
  case Env.lookup name l of
    Just entry -> do
      (t, specialisation) <- specialiseQType src name (view LEnv.value entry)
      tEnv %= LEnv.setUsed name
      requires [ (src, MultiUse name) :< Copy t | view LEnv.used entry ]
      requires [ (src, Captured name) :< Copy t | view LEnv.captured entry ]
      return (t, specialisation)
    Nothing -> throwAt src (NotInScope name)

introTy :: Source -> Name -> Annotated QType -> Praxis ()
introTy src name qTy = do
  l <- use tEnv
  case Env.lookup name l of
    Just _ -> throwAt src $ "variable " <> quote (pretty name) <> " redeclared"
    _      -> tEnv %= LEnv.intro name qTy

introConTy :: Source -> Name -> Annotated QType -> Praxis ()
introConTy src name qTy = do
  l <- use cEnv
  case Env.lookup name l of
    Just _ -> throwAt src $ "constructor " <> quote (pretty name) <> " redeclared"
    _      -> cEnv %= Env.intro name qTy

getConTy :: Source -> Name -> Praxis (Annotated QType)
getConTy src name = do
  l <- use cEnv
  case Env.lookup name l of
    Just t  -> return t
    Nothing -> throwAt src (NotInScope name)

run :: Term a => Annotated a -> Praxis (Annotated a)
run term = do
  term <- generate term
  display term `ifFlag` debug
  requirements' <- use (tySystem . requirements)
  (`ifFlag` debug) $ do
    display (separate "\n\n" (nub . sort $ requirements'))
    use tEnv >>= display
    use cEnv >>= display
  return term

generate :: Term a => Annotated a -> Praxis (Annotated a)
generate term = ($ term) $ case typeof (view value term) of
  IExp     -> generateExp
  IBind    -> generateBind
  IDataCon -> error "standalone DataCon"
  IDecl    -> generateDecl Nothing
  IPat     -> error "standalone Pat"
  _        -> value (recurseTerm generate)

-- Computes in 'parallel' (c.f. `sequence` which computes in series)
-- For our purposes we require each 'branch' to start with the same type environment TODO kEnv etc
-- The output environments are all contextJoined
parallel :: Source -> [Praxis a] -> Praxis [a]
parallel _ []     = return []
parallel _ [x]    = (:[]) <$> x
parallel src (x:xs) = do
  (a, as) <- join src x (parallel src xs)
  return (a:as)

-- TODO move this somewhere
fun :: Annotated Type -> Annotated Type -> Annotated Type
fun a b = TyFun a b `as` phantom KindType

-- TODO use introspection?
patToTy :: Annotated TyPat -> Annotated Type
patToTy = over value patToTy' where
  patToTy' = \case
    TyPatVar n       -> TyVar n
    TyPatViewVar d n -> TyView (phantom (ViewVar d n))
    TyPatPack a b    -> TyPack (patToTy a) (patToTy b)

tyPatToQTyVars :: Annotated TyPat -> [Annotated QTyVar]
tyPatToQTyVars = extract (embedMonoid f) where
  f = \case
    TyPatVar n       -> [ phantom $ QTyVar n ]
    TyPatViewVar d n -> [ phantom $ QViewVar d n ]
    _                -> []

generateDecl :: Maybe (Annotated QType) -> Annotated Decl -> Praxis (Annotated Decl)
generateDecl forwardT (a@(src, _) :< decl) = (a :<) <$> case decl of

  -- TODO Copy constraints needed!
  DeclData mode name arg alts -> do

    -- TODO could be kind annotated to avoid this lookup
    Just k <- kEnv `uses` Env.lookup name

    let
      -- The return type of the constructors
      retTy :: Annotated Type
      retTy = case arg of
        Nothing
          -> TyCon name `as` k
        Just arg | KindFun k1 k2 <- view value k
          -> TyApply (TyCon name `as` k) (patToTy arg) `as` k2

      qTyVars = case arg of
        Nothing  -> []
        Just arg -> tyPatToQTyVars arg

      generateDataCon :: Annotated DataCon -> Praxis (Annotated DataCon)
      generateDataCon ((src, Nothing) :< DataCon name argTy) = do
        let qTy = phantom $ Forall qTyVars [] (fun argTy retTy) -- TODO add src?
        introConTy src name qTy
        return ((src, Just qTy) :< DataCon name argTy)

    alts <- traverse generateDataCon alts
    return $ DeclData mode name arg alts

  DeclEnum name alts -> do
    Just k <- kEnv `uses` Env.lookup name
    let qTy = phantom $ Forall [] [] (TyCon name `as` k)
    mapM_ (\alt -> introConTy src alt qTy) alts
    return $ DeclEnum name alts

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
        ((src, _) :< DeclVar name sig exp)
          | expIsRecSafe exp -> do { ty <- getTyFromSig sig; introTy src name ty; return (ty, decl) }
          | otherwise        -> throwAt src $ "non-function " <> quote (pretty name) <> " can not be recursive"
        _                    -> throwAt src ("illegal non-term in recursive block" :: String)


  DeclSyn name t -> return $ DeclSyn name t

  DeclVar name sig exp -> do

    case sig of

      Nothing -> do
        exp <- generateExp exp
        case forwardT of
          Just (_ :< Forall [] [] t) -> require $ (src, FunCongruence name) :< (t `TEq` view ty exp)
          Nothing                    -> introTy src name (mono (view ty exp))
        return $ DeclVar name Nothing exp

      Just sig@(_ :< Forall boundVars constraints t) -> do
        tySystem . assumptions %= (Set.union (Set.fromList [ view value constraint | constraint <- constraints ])) -- constraints in the signature are added as assumptions
        exp <- generateExp exp
        case forwardT of
          Just _  -> return () -- forwardT is sig, so a FunCongruence constraint is redundant (covered by the below FunSignature constraint)
          Nothing -> introTy src name sig
        require $ (src, FunSignature name) :< (t `TEq` view ty exp)
        return $ DeclVar name (Just sig) exp


generateExp :: Annotated Exp -> Praxis (Annotated Exp)
generateExp (a@(src, _) :< exp) = (\(t :< e) -> (src, Just t) :< e) <$> case exp of

  Apply f x -> do
    rTy <- freshTyUni
    f <- generateExp f
    x <- generateExp x
    let fTy = view ty f
    let xTy = view ty x
    require $ (src, FunApplication) :< (fTy `TEq` fun xTy rTy)
    return (rTy :< Apply f x)

  Case exp alts -> do
    exp <- generateExp exp
    let expTy = view ty exp
    op <- freshTyViewUni RefOrValue
    alts <- parallel src (map (generateAlt op) alts)
    ty1 <- equals (map fst alts) CaseCongruence
    ty2 <- equals (map snd alts) CaseCongruence
    require $ (src, CaseCongruence) :< (expTy `TEq` ty1) -- TODO probably should pick a better name for this
    return (ty2 :< Case exp alts)

  Cases alts -> closure src $ do
    op <- freshTyViewUni RefOrValue
    alts <- parallel src (map (generateAlt op) alts)
    ty1 <- equals (map fst alts) CaseCongruence
    ty2 <- equals (map snd alts) CaseCongruence
    return (fun ty1 ty2 :< Cases alts)

  Con name -> do
    qTy <- getConTy src name
    (t, specialisation) <- specialiseQType src name qTy
    return (t :< Specialise ((src, Just t) :< Con name) specialisation)

  Defer exp1 exp2 -> do
    exp1 <- generateExp exp1
    exp2 <- generateExp exp2
    return (view ty exp1 :< Defer exp1 exp2)

  If condExp thenExp elseExp -> do
    condExp <- generateExp condExp
    (thenExp, elseExp) <- join src (generateExp thenExp) (generateExp elseExp)
    require $ (src,  IfCondition) :< (view ty condExp `TEq` TyCon "Bool" `as` phantom KindType)
    require $ (src, IfCongruence) :< (view ty thenExp `TEq` view ty elseExp)
    return (view ty thenExp :< If condExp thenExp elseExp)

  Lambda pat exp -> closure src $ do
    op <- freshTyViewUni RefOrValue
    (pat, exp) <- generateAlt op (pat, exp)
    return (fun (view ty pat) (view ty exp) :< Lambda pat exp)

  Let bind exp -> scope src $ do
    bind <- generateBind bind
    exp <- generateExp exp
    return (view ty exp :< Let bind exp)

  -- TODO pull from environment?
  Lit lit -> ((\t -> t `as` phantom KindType :< Lit lit) <$>) $ case lit of
    Int  _   -> return $ TyCon "Int"
    Bool _   -> return $ TyCon "Bool"
    Char _   -> return $ TyCon "Char"
    String _ -> do
      op <- freshTyViewUni RefOrValue
      return $ TyApply op (TyCon "String" `as` phantom KindType)

  Read var exp -> scope src $ do
    (refName, refType, specialisation) <- readVar src var
    tEnv %= LEnv.intro var (mono refType)
    exp <- generateExp exp
    let t = view ty exp
    require $ (src, SafeRead) :< RefFree refName t
    -- Reading a polymorphic term is unnecessary (since it's Copyable).
    -- We prohibit since we can't correctly wrap with Specialise (it only makes sense to wrap var, not Read var exp).
    -- TODO should we prohibit all Copy-ables here? It would require a NoCopy / Not constraint.
    when (not (null specialisation)) $ throwAt src $ "read variable " <> quote (pretty var) <> "is polymorphic (read is not necessary)"
    return (t :< Read var exp)

  Pair exp1 exp2 -> do
    exp1 <- generateExp exp1
    exp2 <- generateExp exp2
    let t = TyPair (view ty exp1) (view ty exp2) `as` phantom KindType
    return (t :< Pair exp1 exp2)

  Seq exp1 exp2 -> do
    exp1 <- generateExp exp1
    exp2 <- generateExp exp2
    return (view ty exp2 :< Seq exp1 exp2)

  Sig exp t -> do
    exp <- generateExp exp
    require $ (src, UserSignature) :< (t `TEq` view ty exp)
    return (t :< Sig exp t)

  Switch alts -> do
    conditions <- sequence (map (generateExp . fst) alts)
    requires [ (view source condition, SwitchCondition) :< (view ty condition `TEq` TyCon "Bool" `as` phantom KindType)  | condition <- conditions ]
    exps <- parallel src (map (generateExp . snd) alts)
    t <- equals exps SwitchCongruence
    return (t :< Switch (zip conditions exps))

  Unit -> do
    let t = TyUnit `as` phantom KindType
    return (t :< Unit)

  Var name -> do
    (t, specialisation) <- useVar src name
    return (t :< Specialise ((src, Just t) :< Var name) specialisation)

  Where exp decls -> scope src $ do
    decls <- traverse (generateDecl Nothing) decls
    exp <- generateExp exp
    return (view ty exp :< Where exp decls)


equals :: (Term a, Annotation a ~ Annotated Type) => [Annotated a] -> Reason -> Praxis (Annotated Type)
equals exps = equals' $ map (\((src, Just t) :< _) -> (src, t)) exps where
  equals' :: [(Source, Annotated Type)] -> Reason -> Praxis (Annotated Type)
  equals' ((_, t):ts) reason = requires [ (src, reason) :< (t `TEq` t') | (src, t') <- ts ] >> return t

generateBind :: Annotated Bind -> Praxis (Annotated Bind)
generateBind (a@(src, _) :< Bind pat exp) = do
  exp <- generateExp exp
  op <- freshTyViewUni RefOrValue
  pat <- generatePat op pat
  require $ (src, BindCongruence) :< (view ty pat `TEq` view ty exp)
  return (a :< Bind pat exp)

generateAlt :: Annotated Type -> (Annotated Pat, Annotated Exp) -> Praxis (Annotated Pat, Annotated Exp)
generateAlt op (pat, exp) = scope (view source pat) $ do
  pat <- generatePat op pat
  exp <- generateExp exp
  return (pat, exp)


generatePat :: Annotated Type -> Annotated Pat -> Praxis (Annotated Pat)
generatePat op pat = snd <$> generatePat' pat where

  wrap t = TyApply op t `as` phantom KindType

  generatePat' :: Annotated Pat -> Praxis (Annotated Type, Annotated Pat)
  generatePat' ((src, _) :< pat) = (\(t, t' :< p) -> (t, (src, Just t') :< p)) <$> case pat of

    PatAt name pat -> do
      (t, pat) <- generatePat' pat
      introTy src name (mono t)
      require $ (src, MultiAlias name) :< Copy t
      return (t, wrap t :< PatAt name pat)

    PatData name pat -> do
      qTy <- getConTy src name
      let (_ :< Forall vs cs t) = qTy
      case t of
        (_ :< TyFun argTy retTy) -> do
          (tyRewrite, _) <- specialise src name vs cs
          let (argTy', retTy') = (tyRewrite argTy, tyRewrite retTy)
          (patArgType, pat) <- generatePat' pat
          require $ (src, ConPattern name) :< (patArgType `TEq` argTy')
          return (retTy', wrap retTy' :< PatData name pat)
        _ -> throwAt src $ "missing argument in constructor pattern " <> quote (pretty name)

    PatEnum name -> do
      qTy <- getConTy src name
      let (_ :< Forall vs cs t) = qTy
      case t of
        (_ :< TyFun _ _) -> throwAt src $ "unexpected argument in enum pattern " <> quote (pretty name)
        _                -> do
          return (t, t :< PatEnum name)

    PatHole -> do
      -- Treat this is a variable for drop analysis
      var <- freshVar ""
      t <- freshTyUni
      introTy src var (mono (wrap t))
      return (t, wrap t :< PatVar var)

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
