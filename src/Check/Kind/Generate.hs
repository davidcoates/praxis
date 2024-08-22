{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}

module Check.Kind.Generate
  ( run
  ) where

import           Check.State
import           Common
import qualified Env.Strict      as Env
import           Inbuilts
import           Introspect
import           Praxis
import           Print
import           Term

import           Data.List       (nub, sort)
import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set


require :: Tag (Source, KindReason) KindConstraint -> Praxis ()
require ((src, reason) :< con) = kindCheckState . requirements %= Set.insert ((src, Just reason) :< Requirement con)

getKind :: (Term a, Annotation a ~ Annotated Kind) => Annotated a -> Annotated Kind
getKind term = view (annotation . just) term

run :: Term a => Annotated a -> Praxis (Annotated a)
run term = do
  term <- generate term
  display term `ifFlag` debug
  requirements' <- use (kindCheckState . requirements)
  display (separate "\n\n" (nub . sort $ Set.toList requirements')) `ifFlag` debug
  return term

-- TODO since we ignore annotation of input, could adjust this...
generate :: Term a => Annotated a -> Praxis (Annotated a)
generate term = ($ term) $ case typeof (view value term) of
  IDecl    -> generateDecl
  IType    -> generateType
  IView    -> generateView
  ITyPat   -> generateTyPat
  IQTyVar  -> generateQTyVar
  IDataCon -> generateDataCon
  _        -> value (recurseTerm generate)

introKind :: Source -> Name -> Annotated Kind -> Praxis ()
introKind src name kind = do
  entry <- kEnv `uses` Env.lookup name
  case entry of
    Just _ -> throwAt src $ "type " <> quote (pretty name) <> " redeclared"
    _      -> kEnv %= Env.insert name kind


generateQTyVar :: Annotated QTyVar -> Praxis (Annotated QTyVar)
generateQTyVar (a@(src, _) :< qTyVar) = case qTyVar of

  QTyVar var -> do
    k <- freshKindUni
    introKind src var k
    require $ (src, KindReasonQTyVar (a :< qTyVar)) :< KPlain k
    return ((src, Just k) :< QTyVar var)

  QViewVar domain var -> do
    let k = phantom (KindView domain)
    introKind src var k
    return ((src, Just k) :< QViewVar domain var)


generateView :: Annotated View -> Praxis (Annotated View)
generateView ((src, _) :< v) = case v of

  ViewVar _ var -> do
    Just k <- kEnv `uses` Env.lookup var
    return ((src, Just k) :< v)


generateType :: Annotated Type -> Praxis (Annotated Type)
generateType (a@(src, _) :< ty) = (\(k :< t) -> ((src, Just k) :< t)) <$> case ty of

    TyApply f x -> do
      f <- generateType f
      x <- generateType x
      case getKind f of
        (_ :< KindView _) -> do
          require $ (src, KindReasonTyApply f x) :< (getKind x `KEq` phantom KindType)
          return (phantom KindType :< TyApply f x)
        _ -> do
          k1 <- freshKindUni
          k2 <- freshKindUni
          require $ (src, KindReasonTyApply f x) :< (getKind f `KEq` phantom (KindFn k1 k2))
          require $ (src, KindReasonTyApply f x) :< (getKind x `KSub` k1)
          return (k2 :< TyApply f x)

    TyCon con -> do
      entry <- kEnv `uses` Env.lookup con
      case entry of
        Just k  -> return (k :< TyCon con)
        Nothing -> throwAt src $ "type " <> quote (pretty con) <> " is not in scope"

    TyFn t1 t2 -> do
      t1 <- generateType t1
      t2 <- generateType t2
      require $ (src, KindReasonType t1) :< (getKind t1 `KEq` phantom KindType)
      require $ (src, KindReasonType t2) :< (getKind t2 `KEq` phantom KindType)
      return (phantom KindType :< TyFn t1 t2)

    TyUnit -> do
      return (phantom KindType :< TyUnit)

    TyView view -> do
      view <- generateView view
      return (getKind view :< TyView view)

    TyPair t1 t2 -> do
      t1 <- generateType t1
      t2 <- generateType t2
      require $ (src, KindReasonType t1) :< (getKind t1 `KEq` phantom KindType)
      require $ (src, KindReasonType t2) :< (getKind t2 `KEq` phantom KindType)
      return (phantom KindType :< TyPair t1 t2)

    TyVar var -> do
      Just k <- kEnv `uses` Env.lookup var
      return (k :< TyVar var)


generateTyPat :: Annotated TyPat -> Praxis (Annotated TyPat)
generateTyPat (a@(src, _) :< tyPat) = (\(k :< t) -> (src, Just k) :< t) <$> case tyPat of

  TyPatVar var -> do
    k <- freshKindUni
    introKind src var k
    require $ (src, KindReasonTyPat (a :< tyPat)) :< KPlain k
    return (k :< TyPatVar var)

  TyPatViewVar domain var -> do
    introKind src var (phantom (KindView domain))
    return (phantom (KindView domain) :< TyPatViewVar domain var)


generateDataCon :: Annotated DataCon -> Praxis (Annotated DataCon)
generateDataCon (a@(src, _) :< DataCon name arg) = do
  arg <- generate arg
  let dataCon = (a :< DataCon name arg)
  require $ (src, KindReasonType arg) :< (getKind arg `KEq` phantom KindType) -- TODO should just match kind of data type?
  return dataCon

generateDeclType :: Annotated DeclType -> Praxis (Annotated DeclType)
generateDeclType (a@(src, _) :< ty) = case ty of

  DeclTypeData mode name args alts -> do

    k <- freshKindUni
    when (mode == DataRec) $ introKind src name k
    (args, alts) <- save kEnv $ do
        args <- traverse generate args
        alts <- traverse generate alts
        return (args, alts)
    unless (mode == DataRec) $ introKind src name k
    let
      mkKind args = case args of
        []         -> phantom KindType
        (arg:args) -> phantom (KindFn (getKind arg) (mkKind args))
    require $ (src, KindReasonData name args) :< (k `KEq` mkKind args)
    let
      deduce :: (Annotated Type -> TyConstraint) -> [Annotated Type] -> (InstanceOrigin, Instance)
      deduce mkConstraint args' = (Trivial, IsInstanceOnlyIf [ mkConstraint (sub (embedSub f) conType) | (_ :< DataCon _ conType) <- alts ]) where
        f :: Annotated Type -> Maybe (Annotated Type)
        f (_ :< t) = case t of
          TyVar n                   -> n `lookup` specialisedVars
          TyView (_ :< ViewVar _ n) -> n `lookup` specialisedVars
          _                         -> Nothing
        specialisedVars = zipWith bindTyPat args args' where
          bindTyPat :: Annotated TyPat -> Annotated Type -> (Name, Annotated Type)
          bindTyPat (_ :< TyPatVar n) t       = (n, t)
          bindTyPat (_ :< TyPatViewVar _ n) t = (n, t)

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

    iEnv %= Env.insert name instances
    return $ (src, Just k) :< DeclTypeData mode name args alts

  DeclTypeEnum name alts -> do
    let k = phantom KindType
    introKind src name k
    let
      instances = Map.fromList
        [ ("Clone",   \_ -> (Trivial, IsInstance))
        , ("Dispose", \_ -> (Trivial, IsInstance))
        , ("Copy",    \_ -> (Trivial, IsInstance))
        , ("Capture", \_ -> (Trivial, IsInstance))
        ]
    iEnv %= Env.insert name instances
    return $ (src, Just k) :< DeclTypeEnum name alts


generateDecl :: Annotated Decl -> Praxis (Annotated Decl)
generateDecl (a@(src, _) :< decl) = (a :<) <$> case decl of

  DeclType ty -> DeclType <$> generateDeclType ty

  decl        -> recurseTerm generate decl
