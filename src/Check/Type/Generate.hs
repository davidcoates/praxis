{-# LANGUAGE DataKinds              #-}
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


run :: IsTerm a => Annotated KindCheck a -> Praxis (Annotated TypeCheck a)
run term = do
  term <- generate term
  display TypeCheck "annotated term" term `ifFlag` debug
  requirements' <- use (checkState . typeState . typeSolve . requirements)
  (`ifFlag` debug) $ do
    display TypeCheck "requirements" (separate "\n" (nub . sort $ Set.toList requirements'))
  return term

generate :: IsTerm a => Annotated KindCheck a -> Praxis (Annotated TypeCheck a)
generate term = ($ term) $ case typeof (view value term) of
  BindT           -> generateBind
  DeclT           -> generateDecl
  DeclTermT       -> generateDeclTerm
  DeclTypeT       -> generateDeclType
  ExpT            -> generateExp
  ProgramT        -> auto
  QTypeT          -> auto
  TypeT           -> auto
  TypePatT        -> auto
  TypeConstraintT -> auto
  ty              -> error (show ty)
  where
    auto :: (IsTerm a, Annotation TypeCheck a ~ ()) => Annotated KindCheck a -> Praxis (Annotated TypeCheck a)
    auto ((src, _) :< term) = ((src, ()) :<) <$> recurseTerm generate term

introCon :: Source -> Name -> Annotated TypeCheck QType -> Praxis ()
introCon src name qTy = do
  entry <- (checkState . typeState . conEnv) `uses` Map.lookup name
  case entry of
    Just _ -> throwAt TypeCheck src $ "constructor " <> pretty name <> " redeclared"
    _      -> checkState . typeState . conEnv %= Map.insert name qTy

introVar :: Source -> Name -> Annotated TypeCheck QType -> Praxis Name
introVar src name qTy = do
  entry <- (checkState . typeState . varRename . counts) `uses` Map.lookup name
  let count = case entry of { Just count -> count; Nothing -> 0 }
  let rename = name ++ "_" ++ show count
  checkState . typeState . varRename . counts %= Map.insert name (count + 1)
  checkState . typeState . varRename . renames %= Map.insert name rename
  Nothing <- (checkState . typeState . varEnv) `uses` Map.lookup rename -- sanity check
  checkState . typeState . varEnv %= Map.insert rename (mempty, qTy)
  return rename

introHole :: Annotated TypeCheck QType -> Praxis Name
introHole qTy = do
  name <- freshVar "hole"
  Nothing <- (checkState . typeState . varEnv) `uses` Map.lookup name -- sanity check
  checkState . typeState . varEnv %= Map.insert name (mempty, qTy)
  return name

lookupCon :: Source -> Name -> Praxis (Annotated TypeCheck QType)
lookupCon src name = do
  entry <- (checkState . typeState . conEnv) `uses` Map.lookup name
  case entry of
    Just qTy -> return qTy
    Nothing  -> throwAt TypeCheck src $ "constructor " <> pretty name <> " is not in scope"

lookupVar :: Source -> Name -> Praxis (Name, Usage, Annotated TypeCheck QType)
lookupVar src name =do
  entry <- (checkState . typeState . varRename . renames) `uses` Map.lookup name
  let rename = case entry of { Just rename -> rename; Nothing -> name }
  entry <- (checkState . typeState . varEnv) `uses` Map.lookup rename
  case entry of
    Just (usage, qTy) -> return (rename, usage, qTy)
    Nothing           -> throwAt TypeCheck src $ "variable " <> pretty name <> " is not in scope"

--- | Marks a variable as used, returning the type of the variable.
--- A copy constraint will be generated if the variable has already been used or has been captured.
useVar :: Source -> Name -> Praxis (Name, Annotated TypeCheck Type, Maybe (Specialization TypeCheck))
useVar src name = do
  (rename, usage, qTy) <- lookupVar src name
  (ty, specialization) <- specializeQType src name qTy
  unless (isJust specialization) $ do
    requires [ (src, TypeReasonMultiUse name) :< Requirement (copy ty) | view usedCount usage > 0 ]
  checkState . typeState . varEnv %= Map.adjust (\(usage, qTy) -> (over usedCount (+ 1) usage, qTy)) rename
  return (rename, ty, specialization)

-- | Marks a variable as read, returning the view-type of the variable and the view ref-name.
-- A copy constraint will be generated if the variable has already been used or has been captured.
readVar :: Source -> Name -> Praxis (Name, Name, Annotated TypeCheck Type)
readVar src name = do
  (rename, usage, qTy) <- lookupVar src name
  (ty, specialization) <- specializeQType src name qTy
  -- reading a polymorphic term is illformed (and unnecessary since every specialization is copyable anyway)
  when (isJust specialization) $ throwAt TypeCheck src $ "illegal read of polymorphic variable " <> pretty name
  when (view usedCount usage > 0) $ throwAt TypeCheck src $ "variable " <> pretty name <> " read after use"
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
  series [ throwAt TypeCheck src ("variable " <> pretty name <> " is not used") | name <- unusedVars ]
  return x

require :: Annotated TypeCheck (Requirement TypeConstraint) -> Praxis ()
require requirement = checkState . typeState . typeSolve . requirements %= Set.insert requirement

requires :: [Annotated TypeCheck (Requirement TypeConstraint)] -> Praxis ()
requires = mapM_ require

mono :: Annotated TypeCheck Type -> Annotated TypeCheck QType
mono ty = (view source ty, ()) :< Mono ty

specializeTypePat :: Annotated TypeCheck TypePat -> Praxis (Name, Annotated TypeCheck Type)
specializeTypePat (a :< TypePatVar f n) = (\ty -> (n, a :< view value ty)) <$> freshTypeUni f

specializeQType :: Source -> Name -> Annotated TypeCheck QType -> Praxis (Annotated TypeCheck Type, Maybe (Specialization TypeCheck))
specializeQType src name (_ :< qTy) = case qTy of
  Forall vs cs ty -> do
    vs' <- mapM specializeTypePat vs
    let
      typeRewrite :: IsTerm a => Annotated TypeCheck a -> Annotated TypeCheck a
      typeRewrite = sub (embedSub f)
      f :: Annotated TypeCheck Type -> Maybe (Annotated TypeCheck Type)
      f (_ :< ty) = case ty of
        TypeVar _  n -> n `lookup` vs'
        _            -> Nothing
    let specialization = zip vs (map snd vs')
    requires [ (src, TypeReasonSpecialization name) :< Requirement (typeRewrite c) | c <- cs ]
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

closure :: Source -> Praxis (Tag (Annotated TypeCheck Type) (Exp TypeCheck)) -> Praxis (Tag (Annotated TypeCheck Type) (Exp TypeCheck))
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
  requires [ (src, TypeReasonCaptured name) :< Requirement (capture ty) | (name, (_ :< Mono t)) <- captures ]
  return $ ty :< Capture captures ((src, ty) :< x)

-- Computes in 'parallel' (c.f. `sequence` which computes in series)
-- For our purposes we require each 'branch' to start with the same type environment TODO kEnv etc
-- The output environments are all contextJoined
parallel :: Source -> [Praxis a] -> Praxis [a]
parallel _ []     = return []
parallel _ [x]    = (:[]) <$> x
parallel src (x:xs) = do
  (a, as) <- join src x (parallel src xs)
  return (a:as)

generateDecl :: Annotated KindCheck Decl -> Praxis (Annotated TypeCheck Decl)
generateDecl (a@(src, _) :< decl) = (a :<) <$> case decl of

  DeclRec decls -> do
    let names = [ name | (_ :< DeclRecTerm (_ :< DeclTermVar name _ _)) <- decls ]
    unless (isDistinct names) $ throwAt TypeCheck src ("recursive declarations are not distinct" :: String)
    actions <- mapM preDeclare decls
    decls <- series actions
    return (DeclRec decls)
    where
      getTypeFromSig :: Maybe (Annotated KindCheck QType) -> Praxis (Annotated TypeCheck QType)
      getTypeFromSig = \case
        Nothing  -> mono <$> freshTypeUni Plain
        Just ty  -> generate ty
      preDeclare :: Annotated KindCheck DeclRec -> Praxis (Praxis (Annotated TypeCheck DeclRec))
      preDeclare (a@(src, _) :< decl) = ((a :<) <$>) <$> case decl of
        DeclRecTerm declTerm@(a :< DeclTermVar name sig exp) -> do
          ty <- getTypeFromSig sig
          rename <- introVar src name ty
          return (DeclRecTerm <$> generateDeclTerm' (Just ty) (a :< DeclTermVar rename sig exp))
        DeclRecType declType -> do
           -- FIXME: should pre-declare the constructors ?
          return (DeclRecType <$> generateDeclType declType)

  _ -> recurseTerm generate decl


generateDeclType :: Annotated KindCheck DeclType -> Praxis (Annotated TypeCheck DeclType)
generateDeclType (a@(src, kind) :< ty) = ((src, ()) :<) <$> case ty of

  DeclTypeData mode name typePats alts -> do
    typePats <- traverse generate typePats
    let
      -- The return type of the constructors
      retTy :: Annotated TypeCheck Type
      retTy = foldl (\t1 t2 -> phantom (TypeApply t1 t2)) (phantom (TypeCon name)) (map typePatToType typePats) where
        typePatToType ((src, _) :< TypePatVar flavor name) = (src, ()) :< TypeVar flavor name

      buildConType :: Annotated TypeCheck Type -> Annotated TypeCheck QType
      buildConType argTy = case typePats of
        [] -> phantom (Mono (phantom (TypeFn argTy retTy)))
        _  -> phantom (Forall typePats [] (phantom (TypeFn argTy retTy)))

      generateDataCon :: Annotated KindCheck DataCon -> Praxis (Annotated TypeCheck DataCon)
      generateDataCon ((src, ()) :< DataCon name argTy) = do
        argTy <- generate argTy
        let qTy = buildConType argTy
        introCon src name qTy
        return ((src, qTy) :< DataCon name argTy)

    alts <- traverse generateDataCon alts
    return $ DeclTypeData mode name typePats alts

  DeclTypeEnum name alts -> do
    let qTy = phantom $ Mono (phantom (TypeCon name))
    mapM_ (\alt -> introCon src alt qTy) alts
    return $ DeclTypeEnum name alts


generateDeclTerm ::Annotated KindCheck DeclTerm -> Praxis (Annotated TypeCheck DeclTerm)
generateDeclTerm = generateDeclTerm' Nothing

generateDeclTerm' :: Maybe (Annotated TypeCheck QType) -> Annotated KindCheck DeclTerm -> Praxis (Annotated TypeCheck DeclTerm)
generateDeclTerm' forwardTy (a@(src, _) :< decl) = ((src, ()) :<) <$> case decl of

  DeclTermVar name sig exp -> do
      sig <- traverse generate sig
      case sig of

        Nothing -> do
          exp <- generate exp
          case forwardTy of
            Just (_ :< Mono ty) -> do
              require $ (src, TypeReasonFunctionCongruence name sig) :< Requirement (phantom (TypeIsEq ty (view annotation exp)))
              return $ DeclTermVar name Nothing exp
            Nothing             -> do
              rename <- introVar src name (mono (view annotation exp))
              return $ DeclTermVar rename Nothing exp

        Just sig'@(_ :< Mono ty) -> do
          exp <- generateExp exp
          require $ (src, TypeReasonFunctionCongruence name sig) :< Requirement (phantom (TypeIsEq ty (view annotation exp)))
          case forwardTy of
            Just _  -> do
              -- forwardTy is sig, so a FnCongruence constraint is redundant (covered by the above FnSignature constraint)
              return $ DeclTermVar name sig exp
            Nothing -> do
              rename <- introVar src name sig'
              return $ DeclTermVar rename sig exp

        Just sig'@(_ :< Forall vs cs ty) -> do
          assumeFromQType vs cs -- constraints in the signature are added as assumptions
          exp <- generateExp exp
          require $ (src, TypeReasonFunctionCongruence name sig) :< Requirement (phantom (TypeIsEq ty (view annotation exp)))
          case forwardTy of
            Just _  -> do
              -- forwardTy is sig, so a FnCongruence constraint is redundant (covered by the above FnSignature constraint)
              return $ DeclTermVar name sig exp
            Nothing -> do
              rename <- introVar src name sig'
              return $ DeclTermVar rename sig exp


generateInteger :: Source -> Integer -> Praxis (Annotated TypeCheck Type)
generateInteger src n = do
  ty <- freshTypeUni Value
  require $ (src, TypeReasonIntegerLiteral n) :< Requirement (integral ty)
  require $ (src, TypeReasonIntegerLiteral n) :< Requirement (phantom (TypeIsIntegralOver ty n))
  return $ ty

generateExp :: Annotated KindCheck Exp -> Praxis (Annotated TypeCheck Exp)
generateExp (a@(src, _) :< exp) = (\(ty :< exp) -> (src, ty) :< exp) <$> case exp of

  Apply exp1 exp2 -> do
    retTy <- freshTypeUni Plain
    exp1 <- generateExp exp1
    exp2 <- generateExp exp2
    require $ (src, TypeReasonApply exp1 exp2) :< Requirement (phantom (TypeIsEq (view annotation exp1) (phantom (TypeFn (view annotation exp2) retTy))))
    return (retTy :< Apply exp1 exp2)

  Case exp alts -> do
    exp <- generateExp exp
    alts <- parallel src (map generateAlt alts)
    ty1 <- equals (map fst alts) TypeReasonCaseCongruence
    ty2 <- equals (map snd alts) TypeReasonCaseCongruence
    require $ (src, TypeReasonCaseCongruence) :< Requirement (phantom (TypeIsEq (view annotation exp) ty1)) -- TODO probably should pick a better name for this
    return (ty2 :< Case exp alts)

  Cases alts -> closure src $ do
    alts <- parallel src (map generateAlt alts)
    ty1 <- equals (map fst alts) TypeReasonCaseCongruence
    ty2 <- equals (map snd alts) TypeReasonCaseCongruence
    let ty = phantom (TypeFn ty1 ty2)
    return (ty :< Cases alts)

  Con name -> do
    qTy <- lookupCon src name
    (ty, specialization) <- specializeQType src name qTy
    case specialization of
      Just specialization -> return (ty :< Specialize ((src, ty) :< Con name) specialization)
      Nothing             -> return (ty :< Con name)

  Defer exp1 exp2 -> do
    exp1 <- generateExp exp1
    exp2 <- generateExp exp2
    return (view annotation exp1 :< Defer exp1 exp2)

  If condExp thenExp elseExp -> do
    condExp <- generateExp condExp
    (thenExp, elseExp) <- join src (generateExp thenExp) (generateExp elseExp)
    require $ (src, TypeReasonIfCondition) :< Requirement (phantom (TypeIsEq (view annotation condExp) (phantom (TypeCon "Bool"))))
    require $ (src, TypeReasonIfCongruence) :< Requirement (phantom (TypeIsEq (view annotation thenExp) (view annotation elseExp)))
    return (view annotation thenExp :< If condExp thenExp elseExp)

  Lambda pat exp -> closure src $ do
    pat <- generatePat pat
    exp <- generateExp exp
    let ty = phantom (TypeFn (view annotation pat) (view annotation exp))
    return (ty :< Lambda pat exp)

  Let bind exp -> scope src $ do
    bind <- generateBind bind
    exp <- generateExp exp
    return (view annotation exp :< Let bind exp)

  -- TODO pull from environment?
  Lit lit -> ((\ty -> ty :< Lit lit) <$>) $ case lit of
    Integer n
      -> generateInteger src n
    Bool _
      -> return (phantom (TypeCon "Bool"))
    Char _
      -> return (phantom (TypeCon "Char"))
    String _ -> do
      op <- freshTypeUni View
      return (phantom (TypeApplyOp op (phantom (TypeCon "String"))))

  Read name exp -> do
    (rename, refName, refType) <- readVar src name
    Just (_, qTy) <- (checkState . typeState . varEnv) `uses` Map.lookup rename
    (checkState . typeState . varEnv) %= Map.adjust (\(usage, _) -> (usage, mono refType)) rename
    exp <- generateExp exp
    Just (usage, _) <- (checkState . typeState . varEnv) `uses` Map.lookup rename
    unless (view usedCount usage > 0) $ throwAt TypeCheck src ("variable " <> pretty name <> " is not used in read")
    checkState . typeState . varEnv %= Map.adjust (const (usage, qTy)) rename
    let ty = view annotation exp
    require $ (src, TypeReasonRead name) :< Requirement (phantom (TypeIsRefFree ty refName))
    return (ty :< Read rename exp)

  Pair exp1 exp2 -> do
    exp1 <- generateExp exp1
    exp2 <- generateExp exp2
    let ty = phantom (TypePair (view annotation exp1) (view annotation exp2))
    return (ty :< Pair exp1 exp2)

  Seq exp1 exp2 -> do
    exp1 <- generateExp exp1
    exp2 <- generateExp exp2
    return (view annotation exp2 :< Seq exp1 exp2)

  Sig exp ty -> do
    exp <- generateExp exp
    ty <- generate ty
    require $ (src, TypeReasonSignature ty) :< Requirement (phantom (TypeIsSub (view annotation exp) ty))
    return (ty :< Sig exp ty)

  Switch alts -> do
    conditions <- sequence (map (generateExp . fst) alts)
    requires [ (src, TypeReasonSwitchCondition) :< Requirement (phantom (TypeIsEq ty (phantom (TypeCon "Bool")))) | ((src, ty) :< _) <- conditions ]
    exps <- parallel src (map (generateExp . snd) alts)
    ty <- equals exps TypeReasonSwitchCongruence
    return (ty :< Switch (zip conditions exps))

  Unit -> do
    let ty = phantom TypeUnit
    return (ty :< Unit)

  Var name -> do
    (rename, ty, specialization) <- useVar src name
    case specialization of
      Just specialization -> return (ty :< Specialize ((src, ty) :< Var rename) specialization)
      Nothing             -> return (ty :< Var rename)

  Where exp decls -> scope src $ do
    decls <- traverse generateDeclTerm decls
    exp <- generateExp exp
    return (view annotation exp :< Where exp decls)


equals :: (IsTerm a, Annotation TypeCheck a ~ Annotated TypeCheck Type) => [Annotated TypeCheck a] -> TypeReason -> Praxis (Annotated TypeCheck Type)
equals exps = equals' $ map (\((src, ty) :< _) -> (src, ty)) exps where
  equals' :: [(Source, Annotated TypeCheck Type)] -> TypeReason -> Praxis (Annotated TypeCheck Type)
  equals' ((_, ty):tys) reason = requires [ (src, reason) :< Requirement (phantom (TypeIsEq ty ty')) | (src, ty') <- tys ] >> return ty

generateBind :: Annotated KindCheck Bind -> Praxis (Annotated TypeCheck Bind)
generateBind (a@(src, _) :< Bind pat exp) = do
  exp <- generateExp exp
  pat <- generatePat pat
  require $ (src, TypeReasonBind pat exp) :< Requirement (phantom (TypeIsEq (view annotation pat) (view annotation exp)))
  return (a :< Bind pat exp)

generateAlt ::  (Annotated KindCheck Pat, Annotated KindCheck Exp) -> Praxis (Annotated TypeCheck Pat, Annotated TypeCheck Exp)
generateAlt (pat, exp) = scope (view source pat) $ do
  pat <- generatePat pat
  exp <- generateExp exp
  return (pat, exp)

generatePat :: Annotated KindCheck Pat -> Praxis (Annotated TypeCheck Pat)
generatePat pat = do
  let names = extract (embedMonoid f) pat
      f (_ :< pat) = case pat of
        PatVar n  -> [n]
        PatAt n _ -> [n]
        _         -> []
  unless (isDistinct names) $ throwAt TypeCheck (view source pat) ("variables are not distinct" :: String)
  (_, pat, _) <- generatePat' id pat
  return pat

generatePat' :: (Annotated TypeCheck Type -> Annotated TypeCheck Type) -> Annotated KindCheck Pat -> Praxis (Annotated TypeCheck Type, Annotated TypeCheck Pat, Bool)
generatePat' wrap ((src, _) :< pat) = (\(ty, pat, aliased) -> (ty, (src, wrap ty) :< pat, aliased)) <$> case pat of

  PatAt name pat -> do
    (ty, pat, aliased) <- generatePat' wrap pat
    rename <- introVar src name (mono ty)
    when aliased $ require $ (src, TypeReasonMultiAlias name) :< Requirement (copy ty)
    return (ty, PatAt rename pat, True)

  PatData name pat -> do
    qTy <- lookupCon src name
    (conTy, _) <- specializeQType src name qTy
    case conTy of
      (_ :< TypeFn argTy retTy) -> do
        layer <- freshLayer
        (patArgTy, pat, aliased) <- generatePat' (wrap . layer) pat
        require $ (src, TypeReasonConstructor name) :< Requirement (phantom (TypeIsEq patArgTy argTy))
        return (layer retTy, PatData name pat, aliased)
      _ -> throwAt TypeCheck src $ "missing argument in constructor pattern " <> pretty name

  PatEnum name -> do
    qTy <- lookupCon src name
    let (_ :< Mono conTy) = qTy
    case conTy of
      (_ :< TypeFn _ _) -> throwAt TypeCheck src $ "unexpected argument in enum pattern " <> pretty name
      _  -> do
        return (conTy, PatEnum name, False)

  PatHole -> do
    -- treat this is a variable for drop analysis
    ty <- freshTypeUni Plain
    name <- introHole (mono (wrap ty))
    return (ty, PatVar name, False)

  -- TODO think about how view literals would work, e.g. x@"abc"
  PatLit lit -> (\ty -> (ty, PatLit lit, False)) <$> case lit of
    Bool _    -> return (phantom (TypeCon "Bool"))
    Char _    -> return (phantom (TypeCon "Char"))
    Integer n -> generateInteger src n
    String _  -> return (phantom (TypeCon "String"))

  PatPair pat1 pat2 -> do
    layer <- freshLayer
    (ty1, pat1, aliased1) <- generatePat' (wrap . layer) pat1
    (ty2, pat2, aliased2) <- generatePat' (wrap . layer) pat2
    let ty = layer (phantom (TypePair ty1 ty2))
    return (ty, PatPair pat1 pat2, aliased1 || aliased2)

  PatUnit -> do
    let ty = phantom TypeUnit
    return (ty, PatUnit, False)

  PatVar name -> do
    ty <- freshTypeUni Plain
    rename <- introVar src name (mono (wrap ty))
    return (ty, PatVar rename, True)

  where
    freshLayer :: Praxis (Annotated TypeCheck Type -> Annotated TypeCheck Type)
    freshLayer = do
      op <- freshTypeUni View
      return $ \ty -> phantom (TypeApplyOp op ty)
