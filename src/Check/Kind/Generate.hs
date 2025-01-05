{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}

module Check.Kind.Generate
  ( run
  ) where

import           Check.State
import           Common
import           Inbuilts
import           Introspect
import           Praxis
import           Print
import           Term

import           Data.List       (nub, sort)
import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set


introCon :: Source -> Name -> Annotated Kind -> Praxis ()
introCon src name kind = do
  entry <- (checkState . kindState . typeConEnv) `uses` Map.lookup name
  case entry of
    Just _ -> throwAt src $ "type " <> pretty name <> " redeclared"
    _      -> checkState . kindState . typeConEnv %= Map.insert name kind

introVar :: Source -> Flavor -> Name -> Annotated Kind -> Praxis Name
introVar src flavor name kind = do
  entry <- (checkState . kindState . typeVarRename . counts) `uses` Map.lookup name
  let count = case entry of { Just count -> count; Nothing -> 0 }
  let rename = name ++ "_" ++ show count
  checkState . kindState . typeVarRename . counts %= Map.insert name (count + 1)
  checkState . kindState . typeVarRename . renames %= Map.insert name rename
  Nothing <- (checkState . kindState . typeVarEnv) `uses` Map.lookup rename -- sanity check
  checkState . kindState . typeVarEnv %= Map.insert rename (flavor, kind)
  return rename

lookupCon :: Source -> Name -> Praxis (Annotated Kind)
lookupCon src name = do
  entry <- (checkState . kindState . typeConEnv) `uses` Map.lookup name
  case entry of
    Just kind -> return kind
    Nothing   -> throwAt src $ "type " <> pretty name <> " is not in scope"

lookupVar :: Source -> Flavor -> Name -> Praxis (Name, Annotated Kind)
lookupVar src flavor name = do
  entry <- (checkState . kindState . typeVarRename . renames) `uses` Map.lookup name
  let rename = case entry of { Just rename -> rename; Nothing -> name }
  entry <- (checkState . kindState . typeVarEnv) `uses` Map.lookup rename
  case entry of
    Just (flavor', kind)
      | flavor == flavor' -> return (rename, kind)
      | otherwise         -> throwAt src $ "type variable " <> pretty name <> " has the wrong flavor"
    Nothing -> throwAt src $ "type variable " <> pretty name <> " is not in scope"

checkDistinct :: Source -> [Annotated TypePat] -> Praxis ()
checkDistinct src typePats = do
  let names = map (\(_ :< TypePatVar _ name) -> name) typePats
  unless (isDistinct names) $ throwAt src ("type variables are not distinct" :: String)

scope :: Praxis a -> Praxis a
scope block = save (checkState . kindState . typeVarRename . renames) $ block

require :: Tag (Source, KindReason) KindConstraint -> Praxis ()
require ((src, reason) :< con) = checkState . kindState . kindSolve . requirements %= Set.insert ((src, Just reason) :< Requirement con)

getKind :: (Term a, Annotation a ~ Annotated Kind) => Annotated a -> Annotated Kind
getKind term = view (annotation . just) term

run :: Term a => Annotated a -> Praxis (Annotated a)
run term = do
  term <- generate term
  display "annotated term" term `ifFlag` debug
  requirements' <- use (checkState . kindState . kindSolve . requirements)
  display "requirements" (separate "\n" (nub . sort $ Set.toList requirements')) `ifFlag` debug
  return term

-- TODO since we ignore annotation of input, could adjust this...
generate :: Term a => Annotated a -> Praxis (Annotated a)
generate term = ($ term) $ case typeof (view value term) of
  IDeclTerm -> generateDeclTerm
  IDeclType -> generateDeclType
  IType     -> generateType
  ITypePat  -> generateTypePat
  IDataCon  -> generateDataCon
  IQType    -> generateQType
  _         -> value (recurseTerm generate)

generateType :: Annotated Type -> Praxis (Annotated Type)
generateType (a@(src, _) :< ty) = (\(kind :< ty) -> ((src, Just kind) :< ty)) <$> case ty of

    TypeApply ty1 ty2 -> do
      ty1 <- generateType ty1
      ty2 <- generateType ty2
      argKind <- freshKindUni
      retKind <- freshKindUni
      require $ (src, KindReasonTypeApply ty1 ty2) :< (getKind ty1 `KindIsEq` phantom (KindFn argKind retKind))
      require $ (src, KindReasonTypeApply ty1 ty2) :< (getKind ty2 `KindIsSub` argKind)
      return (retKind :< TypeApply ty1 ty2)

    TypeApplyOp ty1 ty2 -> do
      ty1 <- generateType ty1
      ty2 <- generateType ty2
      require $ (src, KindReasonTypeApplyOp ty1 ty2) :< (getKind ty2 `KindIsEq` phantom KindType)
      return (phantom KindType :< TypeApplyOp ty1 ty2)

    TypeCon con -> do
      kind <- lookupCon src con
      return (kind :< TypeCon con)

    TypeFn ty1 ty2 -> do
      ty1 <- generateType ty1
      ty2 <- generateType ty2
      require $ (src, KindReasonType ty1) :< (getKind ty1 `KindIsEq` phantom KindType)
      require $ (src, KindReasonType ty2) :< (getKind ty2 `KindIsEq` phantom KindType)
      return (phantom KindType :< TypeFn ty1 ty2)

    TypeUnit -> do
      return (phantom KindType :< TypeUnit)

    TypeIdentityOp -> return (phantom KindView :< TypeIdentityOp)

    TypeSetOp tys -> do
      tys <- mapM generateType (Set.toList tys)
      let
        checkRefOrView :: Annotated Type -> Praxis ()
        checkRefOrView ty = case view value (getKind ty) of
          KindRef  -> return ()
          KindView -> return ()
          _        -> throwAt src $ "type " <> pretty ty <> " is in a type operator set but is not a type operator"
      mapM_ checkRefOrView tys
      let
        isRef = all (\op -> case view value (getKind op) of { KindRef -> True; KindView -> False }) tys
      return (phantom (if isRef then KindRef else KindView) :< TypeSetOp (Set.fromList tys))

    TypePair ty1 ty2 -> do
      ty1 <- generateType ty1
      ty2 <- generateType ty2
      require $ (src, KindReasonType ty1) :< (getKind ty1 `KindIsEq` phantom KindType)
      require $ (src, KindReasonType ty2) :< (getKind ty2 `KindIsEq` phantom KindType)
      return (phantom KindType :< TypePair ty1 ty2)

    TypeVar flavor var -> do
      (var, kind) <- lookupVar src flavor var
      return (kind :< TypeVar flavor var)


generateTypePat :: Annotated TypePat -> Praxis (Annotated TypePat)
generateTypePat typePat@(a@(src, _) :< TypePatVar f var) = (\(var, k) -> (src, Just k) :< TypePatVar f var) <$> case f of

  Plain -> do
    kind <- freshKindUni
    var <- introVar src Plain var kind
    require $ (src, KindReasonTypePat typePat) :< KindIsPlain kind
    return (var, kind)

  Ref -> do
    var <- introVar src Ref var (phantom KindRef)
    return (var, phantom KindRef)

  Value -> do
    kind <- freshKindUni
    var <- introVar src Value var kind
    require $ (src, KindReasonTypePat typePat) :< KindIsPlain kind
    return (var, kind)

  View -> do
    var <- introVar src View var (phantom KindView)
    return (var, phantom KindView)


generateDataCon :: Annotated DataCon -> Praxis (Annotated DataCon)
generateDataCon (a@(src, _) :< DataCon name arg) = do
  arg <- generate arg
  let dataCon = (a :< DataCon name arg)
  require $ (src, KindReasonType arg) :< (getKind arg `KindIsEq` phantom KindType) -- TODO should just match kind of data type?
  return dataCon


generateDeclType :: Annotated DeclType -> Praxis (Annotated DeclType)
generateDeclType (a@(src, _) :< ty) = case ty of

  DeclTypeData mode name args alts -> do

    kind <- freshKindUni
    when (mode == DataRec) $ introCon src name kind
    (args, alts) <- scope $ do
        checkDistinct src args
        args <- traverse generate args
        alts <- traverse generate alts
        return (args, alts)
    unless (mode == DataRec) $ introCon src name kind
    let
      mkKind args = case args of
        []         -> phantom KindType
        (arg:args) -> phantom (KindFn (getKind arg) (mkKind args))
    require $ (src, KindReasonData name args) :< (kind `KindIsEq` mkKind args)
    let
      deduce :: (Annotated Type -> TypeConstraint) -> [Annotated Type] -> (InstanceOrigin, Instance)
      deduce mkConstraint args' = (Trivial, IsInstanceOnlyIf [ mkConstraint (sub (embedSub f) conType) | (_ :< DataCon _ conType) <- alts ]) where
        f (_ :< ty) = case ty of
          TypeVar _  n -> n `lookup` specializedVars
          _            -> Nothing
        specializedVars = zip (map (\(a :< TypePatVar _ n) -> n) args) args'

      instances = case mode of
        DataUnboxed -> Map.fromList
          [ ("Clone",          deduce clone)
          , ("Dispose",        deduce dispose)
          , ("Copy",           deduce copy)
          , ("Capture",        deduce capture)
          ]
        _ -> Map.fromList
          [ ("Clone",          deduce clone)
          , ("Dispose",        deduce dispose)
          ]

    checkState . instanceEnv %= Map.insert name instances
    return $ (src, Just kind) :< DeclTypeData mode name args alts

  DeclTypeEnum name alts -> do
    let kind = phantom KindType
    introCon src name kind
    let
      instances = Map.fromList
        [ ("Clone",   \_ -> (Trivial, IsInstance))
        , ("Dispose", \_ -> (Trivial, IsInstance))
        , ("Copy",    \_ -> (Trivial, IsInstance))
        , ("Capture", \_ -> (Trivial, IsInstance))
        ]
    checkState . instanceEnv %= Map.insert name instances
    return $ (src, Just kind) :< DeclTypeEnum name alts


generateDeclTerm :: Annotated DeclTerm -> Praxis (Annotated DeclTerm)
generateDeclTerm (a@(src, _) :< decl) = (a :<) <$> case decl of

  DeclTermVar name (Just sig@(a :< Forall vs _ _)) exp -> scope $ do
    checkDistinct src vs
    sig <- recurse generate sig
    exp <- recurse generate exp
    return $ DeclTermVar name (Just sig) exp

  _                        -> recurseTerm generate decl


generateQType :: Annotated QType -> Praxis (Annotated QType)
generateQType (a@(src, _) :< qTy) = (a :<) <$> case qTy of

  Forall vs _ _ -> checkDistinct src vs >> (scope $ recurseTerm generate qTy)

  _             -> recurseTerm generate qTy
