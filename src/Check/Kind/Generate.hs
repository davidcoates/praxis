{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}

module Check.Kind.Generate
  ( run
  ) where

import           Check.Error
import           Check.Kind.Reason
import           Common
import qualified Env.Env           as Env
import           Introspect
import           Praxis
import           Print
import           Stage
import           Term

import           Data.List         (nub, sort)
import qualified Data.Set          as Set


require :: Tag (Source, Reason) KindConstraint -> Praxis ()
require ((src, reason) :< con) = kindSystem . requirements %= (((src, Just reason) :< Requirement con):)

kind :: (Term a, Functor f, Annotation a ~ Annotated Kind) => (Annotated Kind -> f (Annotated Kind)) -> Annotated a -> f (Annotated a)
kind = annotation . just

run :: Term a => Annotated a -> Praxis (Annotated a)
run term = save stage $ do
  stage .= KindCheck Generate
  term <- generate term
  display term `ifFlag` debug
  requirements' <- use (tySystem . requirements)
  display (separate "\n\n" (nub . sort $ requirements')) `ifFlag` debug
  return term

-- TODO since we ignore annotation of input, could adjust this...
generate :: Term a => Annotated a -> Praxis (Annotated a)
generate term = ($ term) $ case typeof (view value term) of
  IDecl    -> generateDecl
  IType    -> generateTy
  IView    -> generateView
  ITyPat   -> generateTyPat
  IQTyVar  -> generateQTyVar
  IDataCon -> generateDataCon
  _        -> value (recurseTerm generate)

introKind :: Source -> Name -> Annotated Kind -> Praxis ()
introKind s n k = do
  l <- use kEnv
  case Env.lookup n l of
    Just _ -> throwAt s $ "type " <> quote (pretty n) <> " redeclared"
    _      -> kEnv %= Env.intro n k


generateQTyVar :: Annotated QTyVar -> Praxis (Annotated QTyVar)
generateQTyVar (a@(src, _) :< qTyVar) = case qTyVar of

  QTyVar var -> do
    k <- freshKindUni
    introKind src var k
    return ((src, Just k) :< QTyVar var)

  QViewVar domain var -> do
    let k = phantom (KindView domain)
    introKind src var k
    return ((src, Just k) :< QViewVar domain var)


generateView :: Annotated View -> Praxis (Annotated View)
generateView ((src, _) :< v) = case v of

  ViewVar _ var -> do
    entry <- kEnv `uses` Env.lookup var
    case entry of
      Just k  -> return ((src, Just k) :< v)
      Nothing -> throwAt src (NotInScope var)



generateTy :: Annotated Type -> Praxis (Annotated Type)
generateTy (a@(src, _) :< ty) = (\(k :< t) -> ((src, Just k) :< t)) <$> case ty of

    TyApply f x -> do
      f <- generateTy f
      x <- generateTy x
      case view kind f of
        (_ :< KindView _) -> do
          require $ (src, ViewApplication) :< (view kind x `KEq` phantom KindType)
          return (phantom KindType :< TyApply f x)
        _ -> do
          k1 <- freshKindUni
          k2 <- freshKindUni
          require $ (src, TyFunApplication) :< (view kind f `KEq` phantom (KindFun k1 k2))
          require $ (src, TyFunApplication) :< (view kind x `KSub` k1)
          return (k2 :< TyApply f x)

    TyCon con -> do
      entry <- kEnv `uses` Env.lookup con
      case entry of
        Just k  -> return (k :< TyCon con)
        Nothing -> throwAt src (NotInScope con)

    TyFun ty1 ty2 -> do
      ty1 <- generateTy ty1
      ty2 <- generateTy ty2
      require $ (src, FunType) :< (view kind ty1 `KEq` phantom KindType)
      require $ (src, FunType) :< (view kind ty2 `KEq` phantom KindType)
      return (phantom KindType :< TyFun ty1 ty2)

    TyView v -> do
      v <- generateView v
      return (view kind v :< TyView v)

    TyPair ty1 ty2 -> do
      ty1 <- generateTy ty1
      ty2 <- generateTy ty2
      require $ (src, PairType) :< (view kind ty1 `KEq` phantom KindType)
      require $ (src, PairType) :< (view kind ty2 `KEq` phantom KindType)
      return (phantom KindType :< TyPair ty1 ty2)

    TyPack ty1 ty2 -> do
      ty1 <- generateTy ty1
      ty2 <- generateTy ty2
      return (phantom (KindPair (view kind ty1) (view kind ty2)) :< TyPack ty1 ty2)

    TyUnit -> do
      return (phantom KindType :< TyUnit)

    TyVar var -> do
      entry <- kEnv `uses` Env.lookup var
      case entry of
        Just k  -> return (k :< TyVar var)
        Nothing -> throwAt src (NotInScope var)


generateTyPat :: Annotated TyPat -> Praxis (Annotated TyPat)
generateTyPat (a@(src, _) :< tyPat) = (\(k :< t) -> (src, Just k) :< t) <$> case tyPat of

  TyPatVar var -> do
    k <- freshKindUni
    introKind src var k
    return (k :< TyPatVar var)

  TyPatViewVar domain var -> do
    introKind src var (phantom (KindView domain))
    return (phantom (KindView domain) :< TyPatViewVar domain var)

  TyPatPack tyPat1 tyPat2 -> do
    tyPat1 <- generateTyPat tyPat1
    tyPat2 <- generateTyPat tyPat2
    return (phantom (KindPair (view kind tyPat1) (view kind tyPat2)) :< TyPatPack tyPat1 tyPat2)


fun :: Annotated Kind -> Annotated Kind -> Annotated Kind
fun a b = phantom (KindFun a b)

generateDataCon :: Annotated DataCon -> Praxis (Annotated DataCon)
generateDataCon (a@(src, _) :< DataCon name arg) = do
  arg <- generate arg
  require $ (src, DataConType name) :< (view kind arg `KEq` phantom KindType) -- TODO should just match kind of data type?
  return (a :< DataCon name arg)

generateDecl :: Annotated Decl -> Praxis (Annotated Decl)
generateDecl (a@(src, _) :< decl) = (a :<) <$> case decl of

  DeclData mode name arg alts -> do
    k <- freshKindUni
    when (mode == DataRec) $ introKind src name k
    (arg, alts) <- save kEnv $ do
        arg <- traverse generate arg
        alts <- traverse generate alts
        return (arg, alts)
    unless (mode == DataRec) $ introKind src name k
    case arg of
      Nothing  -> require $ (src, DataType name) :< (k `KEq` phantom KindType)
      Just arg -> require $ (src, DataType name) :< (k `KEq` phantom (KindFun (view kind arg) (phantom KindType)))
    return $ DeclData mode name arg alts

  DeclEnum name alts -> do
    introKind src name (phantom KindType)
    return $ DeclEnum name alts

  decl -> recurseTerm generate decl
