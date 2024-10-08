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

import           Check.State
import           Check.Type.Solve (assumeFromQType)
import           Common
import qualified Env.Linear       as LEnv
import qualified Env.Strict       as Env
import           Inbuilts         (capture, copy, integral)
import           Introspect
import           Praxis
import           Print
import           Stage
import           Term

import           Control.Monad    (replicateM)
import           Data.Foldable    (foldMap, foldlM)
import           Data.List        (nub, partition, sort)
import           Data.Maybe       (isJust, mapMaybe)
import qualified Data.Set         as Set
import           Prelude          hiding (log)


require :: Tag (Source, TypeReason) TypeConstraint -> Praxis ()
require ((src, reason) :< con) = typeCheckState . requirements %= Set.insert ((src, Just reason) :< Requirement con)

requires :: [Tag (Source, TypeReason) TypeConstraint] -> Praxis ()
requires = mapM_ require

getType :: (Term a, Annotation a ~ Annotated Type) => Annotated a -> Annotated Type
getType term = view (annotation . just) term

mono :: Annotated Type -> Annotated QType
mono t = (view source t, Nothing) :< Mono t

expIsFunction :: Annotated Exp -> Bool
expIsFunction (_ :< exp) = case exp of
  Lambda _ _ -> True
  Cases  _   -> True
  _          -> False

specialiseTypePat :: Annotated TypePat -> Praxis (Name, Annotated Type)
specialiseTypePat (a :< TypePatVar f n) = (\t -> (n, a :< view value t)) <$> freshTypeUni f

specialiseQType :: Source -> Name -> Annotated QType -> Praxis (Annotated Type, Maybe Specialisation)
specialiseQType src name (_ :< qTy) = case qTy of
  Forall vs cs t -> do
    vs' <- mapM specialiseTypePat vs
    let
      typeRewrite :: Term a => Annotated a -> Annotated a
      typeRewrite = sub (embedSub f)
      f :: Annotated Type -> Maybe (Annotated Type)
      f (_ :< t) = case t of
        TypeVar _  n -> n `lookup` vs'
        _            -> Nothing
    let specialisation = zip vs (map snd vs')
    requires [ (src, TypeReasonSpecialisation name) :< view value (typeRewrite c) | c <- cs ]
    return (typeRewrite t, Just specialisation)
  Mono t -> return (t, Nothing)

join :: Source -> Praxis a -> Praxis b -> Praxis (a, b)
join src branch1 branch2 = do
  e0 <- use tEnv
  x <- branch1
  e1 <- use tEnv
  tEnv .= e0
  y <- branch2
  e2 <- use tEnv
  tEnv .= LEnv.join e1 e2
  return (x, y)

closure :: Source -> Praxis (Tag (Annotated Type) Exp) -> Praxis (Tag (Annotated Type) Exp)
closure src exp = do
  e1 <- use tEnv
  (t :< x) <- scope src exp
  e2 <- use tEnv
  let captures = Env.toList (LEnv.touched e1 e2)
  -- Note: copy restrictions do not apply to polymorphic terms
  requires [ (src, TypeReasonCaptured name) :< capture t | (name, _ :< Mono t) <- captures ]
  return $ t :< Closure captures ((src, Just t) :< x)

scope :: Source -> Praxis a -> Praxis a
scope src block = do
  e1 <- use tEnv
  x <- block
  e2 <- use tEnv
  let
    scopedVars = e2 `LEnv.difference` e1
    unusedVars = [ (n, view LEnv.value e) | (n, e) <- Env.toList scopedVars, view LEnv.used e == 0 && view LEnv.read e == 0 ]
  series $ [ throwAt src ("variable " <> pretty n <> " is not used") | (n, _) <- unusedVars, head n /= '_' ] -- hacky
  tEnv .= e2 `LEnv.difference` scopedVars
  return x

-- | Marks a variable as read, returning the view-type of the variable and the view ref-name.
-- A copy constraint will be generated if the variable has already been used or has been captured.
readVar :: Source -> Name -> Praxis (Name, Annotated Type)
readVar src name = do
  r@(_ :< TypeRef refName) <- freshRef
  Just entry <- tEnv `uses` Env.lookup name
  (t, specialisation) <- specialiseQType src name (view LEnv.value entry)
  when (view LEnv.used entry > 0) $ throwAt src $ "variable " <> pretty name <> " read after use"
  -- reading a polymorphic term is illformed (and unnecessary since every specialisation is copyable anyway)
  when (isJust specialisation) $ throwAt src $ "illegal read of polymorphic variable " <> pretty name
  tEnv %= LEnv.incRead name
  return $ (refName, phantom (TypeApplyOp r t))

-- | Marks a variable as used, returning the type of the variable.
-- A copy constraint will be generated if the variable has already been used or has been captured.
useVar :: Source -> Name -> Praxis (Annotated Type, Maybe Specialisation)
useVar src name = do
  Just entry <- tEnv `uses` Env.lookup name
  (t, specialisation) <- specialiseQType src name (view LEnv.value entry)
  tEnv %= LEnv.incUsed name
  unless (isJust specialisation) $ do
    requires [ (src, TypeReasonMultiUse name) :< copy t | view LEnv.used entry > 0 ]
  return (t, specialisation)

introType :: Source -> Name -> Annotated QType -> Praxis ()
introType src name qTy = do
  entry <- tEnv `uses` Env.lookup name
  case entry of
    Just _ -> throwAt src $ "variable " <> pretty name <> " redeclared"
    _      -> tEnv %= LEnv.insert name qTy

introConType :: Source -> Name -> Annotated QType -> Praxis ()
introConType src name qTy = do
  l <- use cEnv
  case Env.lookup name l of
    Just _ -> throwAt src $ "constructor " <> pretty name <> " redeclared"
    _      -> cEnv %= Env.insert name qTy

getConType :: Source -> Name -> Praxis (Annotated QType)
getConType src name = do
  l <- use cEnv
  case Env.lookup name l of
    Just t  -> return t
    Nothing -> throwAt src $ "constructor " <> pretty name <> " is not in scope"

run :: Term a => Annotated a -> Praxis (Annotated a)
run term = do
  term <- generate term
  display "annotated term" term `ifFlag` debug
  requirements' <- use (typeCheckState . requirements)
  (`ifFlag` debug) $ do
    display "requirements" (separate "\n" (nub . sort $ Set.toList requirements'))
    use tEnv >>= display "environment"
    use cEnv >>= display "constructor environment"
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

generateDeclType :: Annotated DeclType -> Praxis (Annotated DeclType)
generateDeclType (a@(src, Just k) :< ty) = case ty of

  DeclTypeData mode name typePats alts -> do
    let
      -- The return type of the constructors
      retTy :: Annotated Type
      retTy = retTy' (TypeCon name `as` k) typePats where
        retTy' ty = \case
          [] -> ty
          (typePat:typePats) ->
            let
              Just (_ :< KindFn _ k) = view annotation ty
              (a :< TypePatVar f n) = typePat
            in
              retTy' (TypeApply ty (a :< TypeVar f n) `as` k) typePats

      buildConType :: Annotated Type -> Annotated QType
      buildConType argTy = case typePats of
        [] -> phantom $ Mono (TypeFn argTy retTy `as` phantom KindType)
        _  -> phantom $ Forall typePats [] (TypeFn argTy retTy `as` phantom KindType)

      generateDataCon :: Annotated DataCon -> Praxis (Annotated DataCon)
      generateDataCon ((src, Nothing) :< DataCon name argTy) = do
        let qTy = buildConType argTy
        introConType src name qTy
        return ((src, Just qTy) :< DataCon name argTy)

    alts <- traverse generateDataCon alts
    return $ (a :< DeclTypeData mode name typePats alts)

  DeclTypeEnum name alts -> do
    let qTy = phantom $ Mono (TypeCon name `as` k)
    mapM_ (\alt -> introConType src alt qTy) alts
    return $ (a :< DeclTypeEnum name alts)


generateDeclTerm ::Annotated DeclTerm -> Praxis (Annotated DeclTerm)
generateDeclTerm = generateDeclTerm' Nothing

generateDeclTerm' :: Maybe (Annotated QType) -> Annotated DeclTerm -> Praxis (Annotated DeclTerm)
generateDeclTerm' forwardTy (a@(src, _) :< decl) = (a :<) <$> case decl of

  DeclTermRec decls -> do
    terms <- mapM preDeclare decls
    decls <- mapM (\(ty, decl) -> generateDeclTerm' (Just ty) decl) terms
    return $ DeclTermRec decls
    where
      getTypeFromSig = \case
        Nothing -> mono <$> freshTypeUni Plain
        Just ty -> pure ty
      preDeclare decl = case decl of
        ((src, _) :< DeclTermVar name sig exp)
          | expIsFunction exp -> do { ty <- getTypeFromSig sig; introType src name ty; return (ty, decl) }
          | otherwise         -> throwAt src $ "non-function " <> pretty name <> " can not be recursive"

  DeclTermVar name sig exp -> case sig of

      Nothing -> do
        exp <- generateExp exp
        case forwardTy of
          Just (_ :< Mono t) -> require $ (src, TypeReasonFunctionCongruence name sig) :< (t `TypeIsEq` getType exp)
          Nothing            -> introType src name (mono (getType exp))
        return $ DeclTermVar name Nothing exp

      Just sig'@(_ :< Mono t) -> do
        exp <- generateExp exp
        case forwardTy of
          Just _  -> return () -- forwardTy is sig, so a FnCongruence constraint is redundant (covered by the below FnSignature constraint)
          Nothing -> introType src name sig'
        require $ (src, TypeReasonFunctionCongruence name sig) :< (t `TypeIsEq` getType exp)
        return $ DeclTermVar name sig exp

      Just sig'@(_ :< Forall vs cs t) -> do
        when (not (expIsFunction exp)) $ throwAt src $ "non-function " <> pretty name <> " can not be polymorphic"
        assumeFromQType vs cs -- constraints in the signature are added as assumptions
        exp <- generateExp exp
        case forwardTy of
          Just _  -> return () -- forwardTy is sig, so a FnCongruence constraint is redundant (covered by the below FnSignature constraint)
          Nothing -> introType src name sig'
        require $ (src, TypeReasonFunctionCongruence name sig) :< (t `TypeIsEq` getType exp)
        return $ DeclTermVar name sig exp


generateInteger :: Source -> Integer -> Praxis (Annotated Type)
generateInteger src n = do
  t <- freshTypeUni Value
  require $ (src, TypeReasonIntegerLiteral n) :< integral t
  require $ (src, TypeReasonIntegerLiteral n) :< TypeIsIntegralOver t n
  return $ t

generateExp :: Annotated Exp -> Praxis (Annotated Exp)
generateExp (a@(src, _) :< exp) = (\(t :< e) -> (src, Just t) :< e) <$> case exp of

  Apply f x -> do
    rTy <- freshTypeUni Plain
    f <- generateExp f
    x <- generateExp x
    let fTy = getType f
    let xTy = getType x
    require $ (src, TypeReasonApply f x) :< (fTy `TypeIsEq` (TypeFn xTy rTy `as` phantom KindType))
    return (rTy :< Apply f x)

  Case exp alts -> do
    exp <- generateExp exp
    let expTy = getType exp
    alts <- parallel src (map generateAlt alts)
    t1 <- equals (map fst alts) TypeReasonCaseCongruence
    t2 <- equals (map snd alts) TypeReasonCaseCongruence
    require $ (src, TypeReasonCaseCongruence) :< (expTy `TypeIsEq` t1) -- TODO probably should pick a better name for this
    return (t2 :< Case exp alts)

  Cases alts -> closure src $ do
    alts <- parallel src (map generateAlt alts)
    t1 <- equals (map fst alts) TypeReasonCaseCongruence
    t2 <- equals (map snd alts) TypeReasonCaseCongruence
    let t = TypeFn t1 t2 `as` phantom KindType
    return (t :< Cases alts)

  Con name -> do
    qTy <- getConType src name
    (t, specialisation) <- specialiseQType src name qTy
    case specialisation of
      Just specialisation -> return (t :< Specialise ((src, Just t) :< Con name) specialisation)
      Nothing             -> return (t :< Con name)

  Defer exp1 exp2 -> do
    exp1 <- generateExp exp1
    exp2 <- generateExp exp2
    return (getType exp1 :< Defer exp1 exp2)

  If condExp thenExp elseExp -> do
    condExp <- generateExp condExp
    (thenExp, elseExp) <- join src (generateExp thenExp) (generateExp elseExp)
    require $ (src, TypeReasonIfCondition) :< (getType condExp `TypeIsEq` TypeCon "Bool" `as` phantom KindType)
    require $ (src, TypeReasonIfCongruence) :< (getType thenExp `TypeIsEq` getType elseExp)
    return (getType thenExp :< If condExp thenExp elseExp)

  Lambda pat exp -> closure src $ do
    pat <- generatePat pat
    exp <- generateExp exp
    let t = TypeFn (getType pat) (getType exp) `as` phantom KindType
    return (t :< Lambda pat exp)

  Let bind exp -> scope src $ do
    bind <- generateBind bind
    exp <- generateExp exp
    return (getType exp :< Let bind exp)

  -- TODO pull from environment?
  Lit lit -> ((\t -> t :< Lit lit) <$>) $ case lit of
    Integer n
      -> generateInteger src n
    Bool _
      -> return $ TypeCon "Bool" `as` phantom KindType
    Char _
      -> return $ TypeCon "Char" `as` phantom KindType
    String _ -> do
      op <- freshTypeUni View
      return $ TypeApplyOp op (TypeCon "String" `as` phantom KindType) `as` phantom KindType

  Read var exp -> do
    (refName, refType) <- readVar src var
    Just entry <- tEnv `uses` Env.lookup var
    tEnv %= Env.adjust (const (LEnv.mkEntry (mono refType))) var
    exp <- generateExp exp
    Just entry' <- tEnv `uses` Env.lookup var
    unless (view LEnv.used entry' > 0) $ throwAt src ("variable " <> pretty var <> " is not used in read")
    tEnv %= Env.adjust (const entry) var
    let t = getType exp
    require $ (src, TypeReasonRead var) :< TypeIsRefFree t refName
    return (t :< Read var exp)

  Pair exp1 exp2 -> do
    exp1 <- generateExp exp1
    exp2 <- generateExp exp2
    let t = TypePair (getType exp1) (getType exp2) `as` phantom KindType
    return (t :< Pair exp1 exp2)

  Seq exp1 exp2 -> do
    exp1 <- generateExp exp1
    exp2 <- generateExp exp2
    return (getType exp2 :< Seq exp1 exp2)

  Sig exp t -> do
    exp <- generateExp exp
    require $ (src, TypeReasonSignature t) :< (getType exp `TypeIsSub` t)
    return (t :< Sig exp t)

  Switch alts -> do
    conditions <- sequence (map (generateExp . fst) alts)
    requires [ (view source condition, TypeReasonSwitchCondition) :< (getType condition `TypeIsEq` TypeCon "Bool" `as` phantom KindType)  | condition <- conditions ]
    exps <- parallel src (map (generateExp . snd) alts)
    t <- equals exps TypeReasonSwitchCongruence
    return (t :< Switch (zip conditions exps))

  Unit -> do
    let t = TypeUnit `as` phantom KindType
    return (t :< Unit)

  Var name -> do
    (t, specialisation) <- useVar src name
    case specialisation of
      Just specialisation -> return (t :< Specialise ((src, Just t) :< Var name) specialisation)
      Nothing             -> return (t :< Var name)

  Where exp decls -> scope src $ do
    decls <- traverse generateDeclTerm decls
    exp <- generateExp exp
    return (getType exp :< Where exp decls)


equals :: (Term a, Annotation a ~ Annotated Type) => [Annotated a] -> TypeReason -> Praxis (Annotated Type)
equals exps = equals' $ map (\((src, Just t) :< _) -> (src, t)) exps where
  equals' :: [(Source, Annotated Type)] -> TypeReason -> Praxis (Annotated Type)
  equals' ((_, t):ts) reason = requires [ (src, reason) :< (t `TypeIsEq` t') | (src, t') <- ts ] >> return t

generateBind :: Annotated Bind -> Praxis (Annotated Bind)
generateBind (a@(src, _) :< Bind pat exp) = do
  exp <- generateExp exp
  pat <- generatePat pat
  require $ (src, TypeReasonBind pat exp) :< (getType pat `TypeIsEq` getType exp)
  return (a :< Bind pat exp)

generateAlt ::  (Annotated Pat, Annotated Exp) -> Praxis (Annotated Pat, Annotated Exp)
generateAlt (pat, exp) = scope (view source pat) $ do
  pat <- generatePat pat
  exp <- generateExp exp
  return (pat, exp)

generatePat :: Annotated Pat -> Praxis (Annotated Pat)
generatePat pat = do
  (_, pat, _) <- generatePat' id pat
  return pat

generatePat' :: (Annotated Type -> Annotated Type) -> Annotated Pat -> Praxis (Annotated Type, Annotated Pat, Bool)
generatePat' wrap ((src, _) :< pat) = (\(t, p, aliased) -> (t, (src, Just (wrap t)) :< p, aliased)) <$> case pat of

  PatAt name pat -> do
    (t, pat, aliased) <- generatePat' wrap pat
    introType src name (mono t)
    when aliased $ require $ (src, TypeReasonMultiAlias name) :< copy t
    return (t, PatAt name pat, True)

  PatData name pat -> do
    qTy <- getConType src name
    (conTy, _) <- specialiseQType src name qTy
    case conTy of
      (_ :< TypeFn argTy retTy) -> do
        layer <- freshLayer
        (patArgType, pat, aliased) <- generatePat' (wrap . layer) pat
        require $ (src, TypeReasonConstructor name) :< (patArgType `TypeIsEq` argTy)
        return (layer retTy, PatData name pat, aliased)
      _ -> throwAt src $ "missing argument in constructor pattern " <> pretty name

  PatEnum name -> do
    qTy <- getConType src name
    let (_ :< Mono conTy) = qTy
    case conTy of
      (_ :< TypeFn _ _) -> throwAt src $ "unexpected argument in enum pattern " <> pretty name
      _  -> do
        return (conTy, PatEnum name, False)

  PatHole -> do
    -- Treat this is a variable for drop analysis
    var <- freshVar "hole"
    t <- freshTypeUni Plain
    introType src var (mono (wrap t))
    return (t, PatVar var, False)

  -- TODO think about how view literals would work, e.g. x@"abc"
  PatLit lit -> (\t -> (t, PatLit lit, False)) <$> case lit of
    Bool _    -> return $ TypeCon "Bool" `as` phantom KindType
    Char _    -> return $ TypeCon "Char" `as` phantom KindType
    Integer n -> generateInteger src n
    String _  -> return $ TypeCon "String" `as` phantom KindType

  PatPair pat1 pat2 -> do
    layer <- freshLayer
    (t1, pat1, aliased1) <- generatePat' (wrap . layer) pat1
    (t2, pat2, aliased2) <- generatePat' (wrap . layer) pat2
    let t = layer (TypePair t1 t2 `as` phantom KindType)
    return (t, PatPair pat1 pat2, aliased1 || aliased2)

  PatUnit -> do
    let t = TypeUnit `as` phantom KindType
    return (t, PatUnit, False)

  PatVar var -> do
    t <- freshTypeUni Plain
    introType src var (mono (wrap t))
    return (t, PatVar var, True)

  where
    freshLayer :: Praxis (Annotated Type -> Annotated Type)
    freshLayer = do
      op <- freshTypeUni View
      return $ \t -> TypeApplyOp op t `as` phantom KindType
