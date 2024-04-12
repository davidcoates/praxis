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
import           Check.Kind.Require
import           Check.Kind.System
import           Common
import qualified Env.Env            as Env
import           Introspect
import           Praxis
import           Print
import           Stage
import           Term

import           Data.List          (nub, sort)
import qualified Data.Set           as Set

kind :: (Term a, Functor f, Annotation a ~ Annotated Kind) => (Annotated Kind -> f (Annotated Kind)) -> Annotated a -> f (Annotated a)
kind = annotation . just

run :: Term a => Annotated a -> Praxis (Annotated a)
run term = save stage $ do
  stage .= KindCheck Generate
  term <- generate term
  display term `ifFlag` debug
  cs <- use (our . constraints)
  display (separate "\n\n" (nub . sort $ cs)) `ifFlag` debug
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
generateView ((src, _) :< view) = case view of

  ViewVar _ var -> do
    entry <- kEnv `uses` Env.lookup var
    case entry of
      Just k  -> return ((src, Just k) :< view)
      Nothing -> throwAt src (NotInScope var)



generateTy :: Annotated Type -> Praxis (Annotated Type)
generateTy (a@(src, _) :< ty) = (\(k :< t) -> ((src, Just k) :< t)) <$> case ty of

    TyApply f x -> do
      f <- generateTy f
      x <- generateTy x
      case view kind f of
        (_ :< KindView _) -> do
          require $ newConstraint (view kind x `KEq` phantom KindType) ViewApplication src
          return (phantom KindType :< TyApply f x)
        _ -> do
          k1 <- freshKindUni
          k2 <- freshKindUni
          require $ newConstraint (view kind f `KEq` phantom (KindFun k1 k2)) TyFunApplication src
          require $ newConstraint (view kind x `KSub` k1) TyFunApplication src
          return (k2 :< TyApply f x)

    TyCon con -> do
      entry <- kEnv `uses` Env.lookup con
      case entry of
        Just k  -> return (k :< TyCon con)
        Nothing -> throwAt src (NotInScope con)

    TyFun ty1 ty2 -> do
      ty1 <- generateTy ty1
      ty2 <- generateTy ty2
      require $ newConstraint (view kind ty1 `KEq` phantom KindType) FunType src
      require $ newConstraint (view kind ty2 `KEq` phantom KindType) FunType src
      return (phantom KindType :< TyFun ty1 ty2)

    TyView v -> do
      v <- generateView v
      return (view kind v :< TyView v)

    TyPair ty1 ty2 -> do
      ty1 <- generateTy ty1
      ty2 <- generateTy ty2
      require $ newConstraint (view kind ty1 `KEq` phantom KindType) PairType src
      require $ newConstraint (view kind ty2 `KEq` phantom KindType) PairType src
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


generateDataCon :: Annotated DataCon -> Praxis (Annotated DataCon)
generateDataCon (a@(src, _) :< DataCon name arg)
  | Nothing  <- arg = return (a :< DataCon name arg)
  | Just arg <- arg = do
      arg <- generate arg
      require $ newConstraint (view kind arg `KEq` phantom KindType) (DataConType name) src -- TODO should just match kind of data type?
      return (a :< DataCon name (Just arg))

fun :: Annotated Kind -> Annotated Kind -> Annotated Kind
fun a b = phantom (KindFun a b)

generateDecl :: Annotated Decl -> Praxis (Annotated Decl)
generateDecl (a@(src, _) :< decl) = (a :<) <$> case decl of

  -- TODO check no duplicated patterns
  DeclData name arg alts -> do
    k <- freshKindUni
    introKind src name k
    (arg, alts) <- save kEnv $ do
        arg <- traverse generate arg
        alts <- traverse generate alts
        return (arg, alts)
    case arg of
      Nothing  -> require $ newConstraint (k `KEq` phantom KindType) (DataType name) src
      Just arg -> require $ newConstraint (k `KEq` phantom (KindFun (view kind arg) (phantom KindType))) (DataType name) src
    return $ DeclData name arg alts

  decl -> recurseTerm generate decl
