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
import           Inbuilts         (capture, copy, integral)
import           Introspect
import           Praxis
import           Print
import           Stage
import           Term

import           Control.Monad    (replicateM)
import           Data.Foldable    (foldMap, foldlM)
import           Data.List        (nub, partition, sort)
import qualified Data.Map.Strict  as Map
import           Data.Maybe       (isJust, mapMaybe)
import qualified Data.Set         as Set
import           Prelude          hiding (log)



introCon :: Source -> Name -> Annotated QType -> Praxis ()
introCon src name qTy = do
  entry <- (checkState . typeState . conEnv) `uses` Map.lookup name
  case entry of
    Just _ -> throwAt src $ "constructor " <> pretty name <> " redeclared"
    _      -> checkState . typeState . conEnv %= Map.insert name qTy

introVar :: Source -> Name -> Annotated QType -> Praxis Name
introVar src name qTy = do
  entry <- (checkState . typeState . varRename . counts) `uses` Map.lookup name
  let count = case entry of { Just count -> count; Nothing -> 0 }
  let rename = name ++ "_" ++ show count
  checkState . typeState . varRename . counts %= Map.insert name (count + 1)
  checkState . typeState . varRename . renames %= Map.insert name rename
  Nothing <- (checkState . typeState . varEnv) `uses` Map.lookup rename -- sanity check
  checkState . typeState . varEnv %= Map.insert rename (mempty, qTy)
  return rename

introHole :: Annotated QType -> Praxis Name
introHole qTy = do
  name <- freshVar "hole"
  Nothing <- (checkState . typeState . varEnv) `uses` Map.lookup name -- sanity check
  checkState . typeState . varEnv %= Map.insert name (mempty, qTy)
  return name

lookupCon :: Source -> Name -> Praxis (Annotated QType)
lookupCon src name = do
  entry <- (checkState . typeState . conEnv) `uses` Map.lookup name
  case entry of
    Just qTy -> return qTy
    Nothing  -> throwAt src $ "constructor " <> pretty name <> " is not in scope"

lookupVar :: Source -> Name -> Praxis (Name, Usage, Annotated QType)
lookupVar src name =do
  entry <- (checkState . typeState . varRename . renames) `uses` Map.lookup name
  let rename = case entry of { Just rename -> rename; Nothing -> name }
  entry <- (checkState . typeState . varEnv) `uses` Map.lookup rename
  case entry of
    Just (usage, qTy) -> return (rename, usage, qTy)
    Nothing           -> throwAt src $ "variable " <> pretty name <> " is not in scope"

--- | Marks a variable as used, returning the type of the variable.
--- A copy constraint will be generated if the variable has already been used or has been captured.
useVar :: Source -> Name -> Praxis (Name, Annotated Type, Maybe Specialization)
useVar src name = do
  (rename, usage, qTy) <- lookupVar src name
  (ty, specialization) <- specializeQType src name qTy
  unless (isJust specialization) $ do
    requires [ (src, TypeReasonMultiUse name) :< copy ty | view usedCount usage > 0 ]
  checkState . typeState . varEnv %= Map.adjust (\(usage, qTy) -> (over usedCount (+ 1) usage, qTy)) rename
  return (rename, ty, specialization)

-- | Marks a variable as read, returning the view-type of the variable and the view ref-name.
-- A copy constraint will be generated if the variable has already been used or has been captured.
readVar :: Source -> Name -> Praxis (Name, Name, Annotated Type)
readVar src name = do
  (rename, usage, qTy) <- lookupVar src name
  (ty, specialization) <- specializeQType src name qTy
  -- reading a polymorphic term is illformed (and unnecessary since every specialization is copyable anyway)
  when (isJust specialization) $ throwAt src $ "illegal read of polymorphic variable " <> pretty name
  when (view usedCount usage > 0) $ throwAt src $ "variable " <> pretty name <> " read after use"
  checkState . typeState . varEnv %= Map.adjust (\(usage, qTy) -> (over readCount (+ 1) usage, qTy)) rename
  ref@(_ :< TypeRef refName) <- freshRef
  return $ (rename, refName, phantom (TypeApplyOp ref ty))

scope :: Source -> Praxis a -> Praxis a
scope src block = save (checkState . typeState . varRename . renames) $ do
  env0 <- use (checkState . typeState . varEnv)
  x <- block
  env1 <- use (checkState . typeState . varEnv)
  let env2 = env1 `Map.difference` env0
  renames <- use (checkState . typeState . varRename . renames)
  let unusedVars = [ name | (name, rename) <- Map.toList renames, case Map.lookup rename env2 of { Just (usage, _) -> view usedCount usage == 0 && view readCount usage == 0; _ -> False } ]
  series [ throwAt src ("variable " <> pretty name <> " is not used") | name <- unusedVars ]
  return x

require :: Tag (Source, TypeReason) TypeConstraint -> Praxis ()
require ((src, reason) :< con) = checkState . typeState . typeSolve . requirements %= Set.insert ((src, Just reason) :< Requirement con)

requires :: [Tag (Source, TypeReason) TypeConstraint] -> Praxis ()
requires = mapM_ require

getType :: (Term a, Annotation a ~ Annotated Type) => Annotated a -> Annotated Type
getType term = view (annotation . just) term

mono :: Annotated Type -> Annotated QType
mono ty = (view source ty, Nothing) :< Mono ty

expIsFunction :: Annotated Exp -> Bool
expIsFunction (_ :< exp) = case exp of
  Lambda _ _ -> True
  Cases  _   -> True
  _          -> False

specializeTypePat :: Annotated TypePat -> Praxis (Name, Annotated Type)
specializeTypePat (a :< TypePatVar f n) = (\ty -> (n, a :< view value ty)) <$> freshTypeUni f

specializeQType :: Source -> Name -> Annotated QType -> Praxis (Annotated Type, Maybe Specialization)
specializeQType src name (_ :< qTy) = case qTy of
  Forall vs cs ty -> do
    vs' <- mapM specializeTypePat vs
    let
      typeRewrite :: Term a => Annotated a -> Annotated a
      typeRewrite = sub (embedSub f)
      f :: Annotated Type -> Maybe (Annotated Type)
      f (_ :< ty) = case ty of
        TypeVar _  n -> n `lookup` vs'
        _            -> Nothing
    let specialization = zip vs (map snd vs')
    requires [ (src, TypeReasonSpecialization name) :< view value (typeRewrite c) | c <- cs ]
    return (typeRewrite ty, Just specialization)
  Mono ty -> return (ty, Nothing)

join :: Source -> Praxis a -> Praxis b -> Praxis (a, b)
join src branch1 branch2 = do
  env0 <- use (checkState . typeState . varEnv)
  x <- branch1
  env1 <- use (checkState . typeState . varEnv)
  checkState . typeState . varEnv .= env0
  y <- branch2
  env2 <- use (checkState . typeState . varEnv)
  checkState . typeState . varEnv .= Map.intersectionWith (\(u1, qTy) (u2, _) -> (u1 <> u2, qTy)) env1 env2
  return (x, y)

closure :: Source -> Praxis (Tag (Annotated Type) Exp) -> Praxis (Tag (Annotated Type) Exp)
closure src exp = do
  env1 <- use (checkState . typeState . varEnv)
  (ty :< x) <- scope src exp
  env2 <- use (checkState . typeState . varEnv)
--  display "exp" (phantom x) `ifFlag` debug
--  display "env1" (show (map (\(n, (u, _)) -> (n, view usedCount u, view readCount u)) (Map.toList env1))) `ifFlag` debug
--  display "env2" (show (map (\(n, (u, _)) -> (n, view usedCount u, view readCount u)) (Map.toList env2))) `ifFlag` debug
  let captures = Map.toList $ Map.map (\((_, qTy), _) -> qTy) $ Map.filter (\((u1, _), (u2, _)) -> view usedCount u2 > view usedCount u1 || view readCount u2 > view readCount u1) $ Map.intersectionWith (,) env1 env2
--  display "captures" (show (map fst captures)) `ifFlag` debug
  -- Note: copy restrictions do not apply to polymorphic terms
  requires [ (src, TypeReasonCaptured name) :< capture ty | (name, (_ :< Mono t)) <- captures ]
  return $ ty :< Capture captures ((src, Just ty) :< x)

run :: Term a => Annotated a -> Praxis (Annotated a)
run term = do
  term <- generate term
  display "annotated term" term `ifFlag` debug
  requirements' <- use (checkState . typeState . typeSolve . requirements)
  (`ifFlag` debug) $ do
    display "requirements" (separate "\n" (nub . sort $ Set.toList requirements'))
--    use (checkState . typeState . varEnv) >>= display "variable environment"
--    use (checkState . typeState . conEnv) >>= display "constructor environment"
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
generateDeclType (a@(src, Just kind) :< ty) = case ty of

  DeclTypeData mode name typePats alts -> do
    let
      -- The return type of the constructors
      retTy :: Annotated Type
      retTy = retTy' (TypeCon name `as` kind) typePats where
        retTy' ty = \case
          [] -> ty
          (typePat:typePats) ->
            let
              Just (_ :< KindFn _ kind) = view annotation ty
              (a :< TypePatVar flavor name) = typePat
            in
              retTy' (TypeApply ty (a :< TypeVar flavor name) `as` kind) typePats

      buildConType :: Annotated Type -> Annotated QType
      buildConType argTy = case typePats of
        [] -> phantom $ Mono (TypeFn argTy retTy `as` phantom KindType)
        _  -> phantom $ Forall typePats [] (TypeFn argTy retTy `as` phantom KindType)

      generateDataCon :: Annotated DataCon -> Praxis (Annotated DataCon)
      generateDataCon ((src, Nothing) :< DataCon name argTy) = do
        let qTy = buildConType argTy
        introCon src name qTy
        return ((src, Just qTy) :< DataCon name argTy)

    alts <- traverse generateDataCon alts
    return $ (a :< DeclTypeData mode name typePats alts)

  DeclTypeEnum name alts -> do
    let qTy = phantom $ Mono (TypeCon name `as` kind)
    mapM_ (\alt -> introCon src alt qTy) alts
    return $ (a :< DeclTypeEnum name alts)


generateDeclTerm ::Annotated DeclTerm -> Praxis (Annotated DeclTerm)
generateDeclTerm = generateDeclTerm' Nothing

generateDeclTerm' :: Maybe (Annotated QType) -> Annotated DeclTerm -> Praxis (Annotated DeclTerm)
generateDeclTerm' forwardTy (a@(src, _) :< decl) = (a :<) <$> case decl of

  DeclTermRec decls -> do
    let names = map (\(_ :< DeclTermVar name _ _) -> name) decls
    unless (isDistinct names) $ throwAt src ("recursive declarations are not distinct" :: String)
    terms <- mapM preDeclare decls
    decls <- mapM (\(ty, decl) -> generateDeclTerm' (Just ty) decl) terms
    return $ DeclTermRec decls
    where
      getTypeFromSig = \case
        Nothing -> mono <$> freshTypeUni Plain
        Just ty -> pure ty
      preDeclare decl = case decl of
        (a@(src, _) :< DeclTermVar name sig exp)
          | expIsFunction exp -> do { ty <- getTypeFromSig sig; rename <- introVar src name ty; return (ty, a :< DeclTermVar rename sig exp) }
          | otherwise         -> throwAt src $ "non-function " <> pretty name <> " can not be recursive"

  DeclTermVar name sig exp -> case sig of

      Nothing -> do
        exp <- generateExp exp
        case forwardTy of
          Just (_ :< Mono ty) -> do
            require $ (src, TypeReasonFunctionCongruence name sig) :< (ty `TypeIsEq` getType exp)
            return $ DeclTermVar name Nothing exp
          Nothing             -> do
            rename <- introVar src name (mono (getType exp))
            return $ DeclTermVar rename Nothing exp

      Just sig'@(_ :< Mono ty) -> do
        exp <- generateExp exp
        require $ (src, TypeReasonFunctionCongruence name sig) :< (ty `TypeIsEq` getType exp)
        case forwardTy of
          Just _  -> do
            -- forwardTy is sig, so a FnCongruence constraint is redundant (covered by the above FnSignature constraint)
            return $ DeclTermVar name sig exp
          Nothing -> do
            rename <- introVar src name sig'
            return $ DeclTermVar rename sig exp

      Just sig'@(_ :< Forall vs cs ty) -> do
        when (not (expIsFunction exp)) $ throwAt src $ "non-function " <> pretty name <> " can not be polymorphic"
        assumeFromQType vs cs -- constraints in the signature are added as assumptions
        exp <- generateExp exp
        require $ (src, TypeReasonFunctionCongruence name sig) :< (ty `TypeIsEq` getType exp)
        case forwardTy of
          Just _  -> do
            -- forwardTy is sig, so a FnCongruence constraint is redundant (covered by the above FnSignature constraint)
            return $ DeclTermVar name sig exp
          Nothing -> do
            rename <- introVar src name sig'
            return $ DeclTermVar rename sig exp


generateInteger :: Source -> Integer -> Praxis (Annotated Type)
generateInteger src n = do
  ty <- freshTypeUni Value
  require $ (src, TypeReasonIntegerLiteral n) :< integral ty
  require $ (src, TypeReasonIntegerLiteral n) :< TypeIsIntegralOver ty n
  return $ ty

generateExp :: Annotated Exp -> Praxis (Annotated Exp)
generateExp (a@(src, _) :< exp) = (\(ty :< exp) -> (src, Just ty) :< exp) <$> case exp of

  Apply exp1 exp2 -> do
    retTy <- freshTypeUni Plain
    exp1 <- generateExp exp1
    exp2 <- generateExp exp2
    require $ (src, TypeReasonApply exp1 exp2) :< (getType exp1 `TypeIsEq` (TypeFn (getType exp2) retTy `as` phantom KindType))
    return (retTy :< Apply exp1 exp2)

  Case exp alts -> do
    exp <- generateExp exp
    let expTy = getType exp
    alts <- parallel src (map generateAlt alts)
    ty1 <- equals (map fst alts) TypeReasonCaseCongruence
    ty2 <- equals (map snd alts) TypeReasonCaseCongruence
    require $ (src, TypeReasonCaseCongruence) :< (expTy `TypeIsEq` ty1) -- TODO probably should pick a better name for this
    return (ty2 :< Case exp alts)

  Cases alts -> closure src $ do
    alts <- parallel src (map generateAlt alts)
    ty1 <- equals (map fst alts) TypeReasonCaseCongruence
    ty2 <- equals (map snd alts) TypeReasonCaseCongruence
    let ty = TypeFn ty1 ty2 `as` phantom KindType
    return (ty :< Cases alts)

  Con name -> do
    qTy <- lookupCon src name
    (ty, specialization) <- specializeQType src name qTy
    case specialization of
      Just specialization -> return (ty :< Specialize ((src, Just ty) :< Con name) specialization)
      Nothing             -> return (ty :< Con name)

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
    let ty = TypeFn (getType pat) (getType exp) `as` phantom KindType
    return (ty :< Lambda pat exp)

  Let bind exp -> scope src $ do
    bind <- generateBind bind
    exp <- generateExp exp
    return (getType exp :< Let bind exp)

  -- TODO pull from environment?
  Lit lit -> ((\ty -> ty :< Lit lit) <$>) $ case lit of
    Integer n
      -> generateInteger src n
    Bool _
      -> return $ TypeCon "Bool" `as` phantom KindType
    Char _
      -> return $ TypeCon "Char" `as` phantom KindType
    String _ -> do
      op <- freshTypeUni View
      return $ TypeApplyOp op (TypeCon "String" `as` phantom KindType) `as` phantom KindType

  Read name exp -> do
    (rename, refName, refType) <- readVar src name
    Just (_, qTy) <- (checkState . typeState . varEnv) `uses` Map.lookup rename
    (checkState . typeState . varEnv) %= Map.adjust (\(usage, _) -> (usage, mono refType)) rename
    exp <- generateExp exp
    Just (usage, _) <- (checkState . typeState . varEnv) `uses` Map.lookup rename
    unless (view usedCount usage > 0) $ throwAt src ("variable " <> pretty name <> " is not used in read")
    checkState . typeState . varEnv %= Map.adjust (const (usage, qTy)) rename
    let ty = getType exp
    require $ (src, TypeReasonRead name) :< TypeIsRefFree ty refName
    return (ty :< Read rename exp)

  Pair exp1 exp2 -> do
    exp1 <- generateExp exp1
    exp2 <- generateExp exp2
    let ty = TypePair (getType exp1) (getType exp2) `as` phantom KindType
    return (ty :< Pair exp1 exp2)

  Seq exp1 exp2 -> do
    exp1 <- generateExp exp1
    exp2 <- generateExp exp2
    return (getType exp2 :< Seq exp1 exp2)

  Sig exp ty -> do
    exp <- generateExp exp
    require $ (src, TypeReasonSignature ty) :< (getType exp `TypeIsSub` ty)
    return (ty :< Sig exp ty)

  Switch alts -> do
    conditions <- sequence (map (generateExp . fst) alts)
    requires [ (view source condition, TypeReasonSwitchCondition) :< (getType condition `TypeIsEq` TypeCon "Bool" `as` phantom KindType)  | condition <- conditions ]
    exps <- parallel src (map (generateExp . snd) alts)
    ty <- equals exps TypeReasonSwitchCongruence
    return (ty :< Switch (zip conditions exps))

  Unit -> do
    let ty = TypeUnit `as` phantom KindType
    return (ty :< Unit)

  Var name -> do
    (rename, ty, specialization) <- useVar src name
    case specialization of
      Just specialization -> return (ty :< Specialize ((src, Just ty) :< Var rename) specialization)
      Nothing             -> return (ty :< Var rename)

  Where exp decls -> scope src $ do
    decls <- traverse generateDeclTerm decls
    exp <- generateExp exp
    return (getType exp :< Where exp decls)


equals :: (Term a, Annotation a ~ Annotated Type) => [Annotated a] -> TypeReason -> Praxis (Annotated Type)
equals exps = equals' $ map (\((src, Just ty) :< _) -> (src, ty)) exps where
  equals' :: [(Source, Annotated Type)] -> TypeReason -> Praxis (Annotated Type)
  equals' ((_, ty):tys) reason = requires [ (src, reason) :< (ty `TypeIsEq` ty') | (src, ty') <- tys ] >> return ty

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
  let names = extract (embedMonoid f) pat
      f = \case
        PatVar n  -> [n]
        PatAt n _ -> [n]
        _         -> []
  unless (isDistinct names) $ throwAt (view source pat) ("variables are not distinct" :: String)
  (_, pat, _) <- generatePat' id pat
  return pat

generatePat' :: (Annotated Type -> Annotated Type) -> Annotated Pat -> Praxis (Annotated Type, Annotated Pat, Bool)
generatePat' wrap ((src, _) :< pat) = (\(ty, pat, aliased) -> (ty, (src, Just (wrap ty)) :< pat, aliased)) <$> case pat of

  PatAt name pat -> do
    (ty, pat, aliased) <- generatePat' wrap pat
    rename <- introVar src name (mono ty)
    when aliased $ require $ (src, TypeReasonMultiAlias name) :< copy ty
    return (ty, PatAt rename pat, True)

  PatData name pat -> do
    qTy <- lookupCon src name
    (conTy, _) <- specializeQType src name qTy
    case conTy of
      (_ :< TypeFn argTy retTy) -> do
        layer <- freshLayer
        (patArgType, pat, aliased) <- generatePat' (wrap . layer) pat
        require $ (src, TypeReasonConstructor name) :< (patArgType `TypeIsEq` argTy)
        return (layer retTy, PatData name pat, aliased)
      _ -> throwAt src $ "missing argument in constructor pattern " <> pretty name

  PatEnum name -> do
    qTy <- lookupCon src name
    let (_ :< Mono conTy) = qTy
    case conTy of
      (_ :< TypeFn _ _) -> throwAt src $ "unexpected argument in enum pattern " <> pretty name
      _  -> do
        return (conTy, PatEnum name, False)

  PatHole -> do
    -- treat this is a variable for drop analysis
    ty <- freshTypeUni Plain
    name <- introHole (mono (wrap ty))
    return (ty, PatVar name, False)

  -- TODO think about how view literals would work, e.g. x@"abc"
  PatLit lit -> (\ty -> (ty, PatLit lit, False)) <$> case lit of
    Bool _    -> return $ TypeCon "Bool" `as` phantom KindType
    Char _    -> return $ TypeCon "Char" `as` phantom KindType
    Integer n -> generateInteger src n
    String _  -> return $ TypeCon "String" `as` phantom KindType

  PatPair pat1 pat2 -> do
    layer <- freshLayer
    (ty1, pat1, aliased1) <- generatePat' (wrap . layer) pat1
    (ty2, pat2, aliased2) <- generatePat' (wrap . layer) pat2
    let ty = layer (TypePair ty1 ty2 `as` phantom KindType)
    return (ty, PatPair pat1 pat2, aliased1 || aliased2)

  PatUnit -> do
    let ty = TypeUnit `as` phantom KindType
    return (ty, PatUnit, False)

  PatVar name -> do
    ty <- freshTypeUni Plain
    rename <- introVar src name (mono (wrap ty))
    return (ty, PatVar rename, True)

  where
    freshLayer :: Praxis (Annotated Type -> Annotated Type)
    freshLayer = do
      op <- freshTypeUni View
      return $ \ty -> TypeApplyOp op ty `as` phantom KindType
