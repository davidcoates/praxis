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
import           Common
import           Env.Env       (Env (..))
import qualified Env.Env       as Env
import qualified Env.LEnv      as LEnv
import           Inbuilts      (copy, fn, integral, pair, unit)
import           Introspect
import           Praxis
import           Print
import           Stage
import           Term

import           Control.Monad (replicateM)
import           Data.Foldable (foldMap, foldlM)
import           Data.List     (nub, partition, sort)
import           Data.Maybe    (isJust, mapMaybe)
import qualified Data.Set      as Set
import           Prelude       hiding (log)


require :: Tag (Source, TyReason) TyConstraint -> Praxis ()
require ((src, reason) :< con) = tySystem . requirements %= (((src, Just reason) :< Requirement con):)

requires :: [Tag (Source, TyReason) TyConstraint] -> Praxis ()
requires = mapM_ require

ty :: (Term a, Functor f, Annotation a ~ Annotated Type) => (Annotated Type -> f (Annotated Type)) -> Annotated a -> f (Annotated a)
ty = annotation . just

mono :: Annotated Type -> Annotated QType
mono t = (view source t, Nothing) :< Forall [] [] t

expIsFunction :: Annotated Exp -> Bool
expIsFunction (_ :< exp) = case exp of
  Lambda _ _ -> True
  Cases  _   -> True
  _          -> False

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
  let specialisation = zip vars (map snd specialisedVars)
  requires [ (src, Specialisation name) :< view value (tyRewrite c) | c <- cs ]
  return (tyRewrite, specialisation)

specialiseQType :: Source -> Name -> Annotated QType -> Praxis (Annotated Type, Maybe Specialisation)
specialiseQType src name (_ :< Forall vs cs t) = case vs of
  [] -> return (t, Nothing)
  _  -> do
    (tyRewrite, specialisation) <- specialise src name vs cs
    return (tyRewrite t, Just specialisation)

join :: Source -> Praxis a -> Praxis b -> Praxis (a, b)
join src branch1 branch2 = do
  l0 <- use tEnv
  x <- branch1
  l1 <- use tEnv
  tEnv .= l0
  y <- branch2
  l2 <- use tEnv
  tEnv .= LEnv.join l1 l2
  return (x, y)

closure :: Source -> Praxis a -> Praxis a
closure src block = do
  Env l1 <- use tEnv
  x <- scope src block
  Env l2 <- use tEnv
  let captured = [ (name, view LEnv.value e1) | (name, e1) <- l1, (_, e2) <- l2, LEnv.touched e2 && not (LEnv.touched e1) ]
  -- Note: copy restrictions do not apply to polymorphic terms
  requires [ (src, Captured name) :< Instance (copy t) | (name, _ :< Forall vs _ t) <- captured, null vs ]
  return x

scope :: Source -> Praxis a -> Praxis a
scope src block = do
  Env l1 <- use tEnv
  x <- block
  Env l2 <- use tEnv
  let n = length l2 - length l1
      (newVars, oldVars) = splitAt n l2
      unusedVars = [ (n, view LEnv.value e) | (n, e) <- newVars, not (LEnv.touched e) ]
  series $ [ throwAt src (Unused n) | (n, _) <- unusedVars, head n /= '_' ] -- hacky
  tEnv .= Env oldVars
  return x

-- | Marks a variable as read, returning the view-type of the variable and the view ref-name.
-- A Copy constraint will be generated if the variable has already been used or has been captured.
readVar :: Source -> Name -> Praxis (Name, Annotated Type)
readVar src name = do
  l <- use tEnv
  r@(_ :< ViewRef refName) <- freshViewRef
  case Env.lookup name l of
    Just entry -> do
      (t, specialisation) <- specialiseQType src name (view LEnv.value entry)
      -- reading a polymorphic term is illformed (and unnecessary since every specialisation is copyable anyway)
      when (isJust specialisation) $ throwAt src $ "illegal read of polymorphic variable " <> quote (pretty name)
      tEnv %= LEnv.setRead name
      when (view LEnv.used entry) $ throwAt src $ "variable " <> quote (pretty name) <> " read after use"
      -- require read variables to *not* be copyable (if the variable is copyable, the read is unnecessary)
      require $ (src, TyReasonRead name) :< Not (phantom (Instance (copy t)))
      return $ (refName, phantom (TyApply (phantom (TyView r)) t))
    Nothing -> throwAt src (NotInScope name)

-- | Marks a variable as used, returning the type of the variable.
-- A Copy constraint will be generated if the variable has already been used or has been captured.
useVar :: Source -> Name -> Praxis (Annotated Type, Maybe Specialisation)
useVar src name = do
  l <- use tEnv
  case Env.lookup name l of
    Just entry -> do
      (t, specialisation) <- specialiseQType src name (view LEnv.value entry)
      tEnv %= LEnv.setUsed name
      unless (isJust specialisation) $ do
        requires [ (src, MultiUse name) :< Instance (copy t) | view LEnv.used entry ]
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
  IBind     -> generateBind
  IDataCon  -> error "standalone DataCon"
  IDeclTerm -> generateDeclTerm
  IDeclType -> generateDeclType
  IExp      -> generateExp
  IPat      -> error "standalone Pat"
  _         -> value (recurseTerm generate)

-- Computes in 'parallel' (c.f. `sequence` which computes in series)
-- For our purposes we require each 'branch' to start with the same type environment TODO kEnv etc
-- The output environments are all contextJoined
parallel :: Source -> [Praxis a] -> Praxis [a]
parallel _ []     = return []
parallel _ [x]    = (:[]) <$> x
parallel src (x:xs) = do
  (a, as) <- join src x (parallel src xs)
  return (a:as)

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

generateDeclType :: Annotated DeclType -> Praxis (Annotated DeclType)
generateDeclType (a@(src, Just k) :< ty) = case ty of

  DeclTypeData mode name arg alts -> do
    let
      -- The return type of the constructors
      retTy :: Annotated Type
      retTy = case arg of
        Nothing
          -> TyCon name `as` k
        Just arg | KindFn k1 k2 <- view value k
          -> TyApply (TyCon name `as` k) (patToTy arg) `as` k2

      qTyVars = case arg of
        Nothing  -> []
        Just arg -> tyPatToQTyVars arg

      generateDataCon :: Annotated DataCon -> Praxis (Annotated DataCon)
      generateDataCon ((src, Nothing) :< DataCon name argTy) = do
        let qTy = phantom $ Forall qTyVars [] (fn argTy retTy) -- TODO add src?
        introConTy src name qTy
        return ((src, Just qTy) :< DataCon name argTy)

    alts <- traverse generateDataCon alts

    return $ (a :< DeclTypeData mode name arg alts)

  DeclTypeEnum name alts -> do
    let qTy = phantom $ Forall [] [] (TyCon name `as` k)
    mapM_ (\alt -> introConTy src alt qTy) alts
    return $ (a :< DeclTypeEnum name alts)


generateDeclTerm ::Annotated DeclTerm -> Praxis (Annotated DeclTerm)
generateDeclTerm = generateDeclTerm' Nothing

generateDeclTerm' :: Maybe (Annotated QType) -> Annotated DeclTerm -> Praxis (Annotated DeclTerm)
generateDeclTerm' forwardT (a@(src, _) :< decl) = (a :<) <$> case decl of

  DeclTermRec decls -> do
    terms <- mapM preDeclare decls
    decls <- mapM (\(ty, decl) -> generateDeclTerm' (Just ty) decl) terms
    return $ DeclTermRec decls
    where
      getTyFromSig = \case
        Nothing -> mono <$> freshTyUni
        Just ty -> pure ty
      preDeclare decl = case decl of
        ((src, _) :< DeclTermVar name sig exp)
          | expIsFunction exp -> do { ty <- getTyFromSig sig; introTy src name ty; return (ty, decl) }
          | otherwise         -> throwAt src $ "non-function " <> quote (pretty name) <> " can not be recursive"

  DeclTermVar name sig exp -> do
    case sig of
      Nothing -> do
        exp <- generateExp exp
        case forwardT of
          Just (_ :< Forall [] [] t) -> require $ (src, FnCongruence name) :< (t `TEq` view ty exp)
          Nothing                    -> introTy src name (mono (view ty exp))
        return $ DeclTermVar name Nothing exp
      Just sig@(_ :< Forall boundVars constraints t) -> do
        when (not (null boundVars) && not (expIsFunction exp)) $ throwAt src $ "non-function " <> quote (pretty name) <> " can not be polymorphic"
        tySystem . assumptions %= (Set.union (Set.fromList [ view value constraint | constraint <- constraints ])) -- constraints in the signature are added as assumptions
        exp <- generateExp exp
        case forwardT of
          Just _  -> return () -- forwardT is sig, so a FnCongruence constraint is redundant (covered by the below FnSignature constraint)
          Nothing -> introTy src name sig
        require $ (src, FnSignature name) :< (t `TEq` view ty exp)
        return $ DeclTermVar name (Just sig) exp


generateInteger :: Source -> Integer -> Praxis (Annotated Type)
generateInteger src n = do
  t <- freshTyUni
  require $ (src, TyReasonIntegerLiteral n) :< Instance (integral t)
  require $ (src, TyReasonIntegerLiteral n) :< HoldsInteger n t
  return $ t

generateExp :: Annotated Exp -> Praxis (Annotated Exp)
generateExp (a@(src, _) :< exp) = (\(t :< e) -> (src, Just t) :< e) <$> case exp of

  Apply f x -> do
    rTy <- freshTyUni
    f <- generateExp f
    x <- generateExp x
    let fTy = view ty f
    let xTy = view ty x
    require $ (src, TyReasonApply f x) :< (fTy `TEq` fn xTy rTy)
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
    return (fn ty1 ty2 :< Cases alts)

  Con name -> do
    qTy <- getConTy src name
    (t, specialisation) <- specialiseQType src name qTy
    case specialisation of
      Just specialisation -> return (t :< Specialise ((src, Just t) :< Con name) specialisation)
      Nothing             -> return (t :< Con name)

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
    return (fn (view ty pat) (view ty exp) :< Lambda pat exp)

  Let bind exp -> scope src $ do
    bind <- generateBind bind
    exp <- generateExp exp
    return (view ty exp :< Let bind exp)

  -- TODO pull from environment?
  Lit lit -> ((\t -> t :< Lit lit) <$>) $ case lit of
    Integer n
      -> generateInteger src n
    Bool _
      -> return $ TyCon "Bool" `as` phantom KindType
    Char _
      -> return $ TyCon "Char" `as` phantom KindType
    String _ -> do
      op <- freshTyViewUni RefOrValue
      return $ TyApply op (TyCon "String" `as` phantom KindType) `as` phantom KindType

  Read var exp -> scope src $ do
    (refName, refType) <- readVar src var
    tEnv %= LEnv.intro var (mono refType)
    exp <- generateExp exp
    let t = view ty exp
    require $ (src, TyReasonRead var) :< RefFree refName t
    return (t :< Read var exp)

  Pair exp1 exp2 -> do
    exp1 <- generateExp exp1
    exp2 <- generateExp exp2
    return (pair (view ty exp1) (view ty exp2) :< Pair exp1 exp2)

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
    return (unit :< Unit)

  Var name -> do
    (t, specialisation) <- useVar src name
    case specialisation of
      Just specialisation -> return (t :< Specialise ((src, Just t) :< Var name) specialisation)
      Nothing             -> return (t :< Var name)

  Where exp decls -> scope src $ do
    decls <- traverse generateDeclTerm decls
    exp <- generateExp exp
    return (view ty exp :< Where exp decls)


equals :: (Term a, Annotation a ~ Annotated Type) => [Annotated a] -> TyReason -> Praxis (Annotated Type)
equals exps = equals' $ map (\((src, Just t) :< _) -> (src, t)) exps where
  equals' :: [(Source, Annotated Type)] -> TyReason -> Praxis (Annotated Type)
  equals' ((_, t):ts) reason = requires [ (src, reason) :< (t `TEq` t') | (src, t') <- ts ] >> return t

generateBind :: Annotated Bind -> Praxis (Annotated Bind)
generateBind (a@(src, _) :< Bind pat exp) = do
  exp <- generateExp exp
  op <- freshTyViewUni RefOrValue
  pat <- generatePat op pat
  require $ (src, TyReasonBind pat exp) :< (view ty pat `TEq` view ty exp)
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
      require $ (src, MultiAlias name) :< Instance (copy t)
      return (t, wrap t :< PatAt name pat)

    PatData name pat -> do
      qTy <- getConTy src name
      let (_ :< Forall vs cs t) = qTy
      case t of
        (_ :< TyApply (_ :< TyCon "Fn") (_ :< TyPack argTy retTy)) -> do
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
        (_ :< TyApply (_ :< TyCon "Fn") _) -> throwAt src $ "unexpected argument in enum pattern " <> quote (pretty name)
        _  -> do
          return (t, t :< PatEnum name)

    PatHole -> do
      -- Treat this is a variable for drop analysis
      var <- freshVar ""
      t <- freshTyUni
      introTy src var (mono (wrap t))
      return (t, wrap t :< PatVar var)

    -- TODO think about how view literals would work, e.g. x@"abc"
    PatLit lit -> (\t -> (t, t :< PatLit lit)) <$> case lit of
      Bool _    -> return $ TyCon "Bool" `as` phantom KindType
      Char _    -> return $ TyCon "Char" `as` phantom KindType
      Integer n -> generateInteger src n
      String _  -> return $ TyCon "String" `as` phantom KindType

    PatPair pat1 pat2 -> do
      (t1, pat1) <- generatePat' pat1
      (t2, pat2) <- generatePat' pat2
      let t = pair t1 t2
      return (t, wrap t :< PatPair pat1 pat2)

    PatUnit -> do
      let t = unit
      return (t, t :< PatUnit)

    PatVar var -> do
      t <- freshTyUni
      introTy src var (mono (wrap t))
      return (t, wrap t :< PatVar var)
