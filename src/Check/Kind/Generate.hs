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
import           Common
import qualified Env.Env         as Env
import           Inbuilts
import           Introspect
import           Praxis
import           Print
import           Stage
import           Term

import           Data.List       (nub, sort)
import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set


require :: Tag (Source, KindReason) KindConstraint -> Praxis ()
require ((src, reason) :< con) = kindSystem . requirements %= (((src, Just reason) :< Requirement con):)

kind :: (Term a, Functor f, Annotation a ~ Annotated Kind) => (Annotated Kind -> f (Annotated Kind)) -> Annotated a -> f (Annotated a)
kind = annotation . just

run :: Term a => Annotated a -> Praxis (Annotated a)
run term = do
  term <- generate term
  display term `ifFlag` debug
  requirements' <- use (kindSystem . requirements)
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
          require $ (src, KindReasonTyApply f x) :< (view kind x `KEq` phantom KindType)
          return (phantom KindType :< TyApply f x)
        _ -> do
          k1 <- freshKindUni
          k2 <- freshKindUni
          require $ (src, KindReasonTyApply f x) :< (view kind f `KEq` phantom (KindFun k1 k2))
          require $ (src, KindReasonTyApply f x) :< (view kind x `KSub` k1)
          return (k2 :< TyApply f x)

    TyCon con -> do
      entry <- kEnv `uses` Env.lookup con
      case entry of
        Just k  -> return (k :< TyCon con)
        Nothing -> throwAt src (NotInScope con)

    TyView v -> do
      v <- generateView v
      return (view kind v :< TyView v)

    TyPack ty1 ty2 -> do
      ty1 <- generateTy ty1
      ty2 <- generateTy ty2
      return (phantom (KindPair (view kind ty1) (view kind ty2)) :< TyPack ty1 ty2)

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
generateDataCon (a@(src, _) :< DataCon name arg) = do
  arg <- generate arg
  let dataCon = (a :< DataCon name arg)
  require $ (src, KindReasonType arg) :< (view kind arg `KEq` phantom KindType) -- TODO should just match kind of data type?
  return dataCon

generateDeclType :: Annotated DeclType -> Praxis (Annotated DeclType)
generateDeclType (a@(src, _) :< ty) = case ty of

  DeclTypeData mode name arg alts -> do

    k <- freshKindUni
    when (mode == DataRec) $ introKind src name k
    (arg, alts) <- save kEnv $ do
        arg <- traverse generate arg
        alts <- traverse generate alts
        return (arg, alts)
    unless (mode == DataRec) $ introKind src name k
    case arg of
      Nothing  -> require $ (src, KindReasonData name Nothing)    :< (k `KEq` phantom KindType)
      Just arg -> require $ (src, KindReasonData name (Just arg)) :< (k `KEq` phantom (KindFun (view kind arg) (phantom KindType)))

    let
      deduce :: (Annotated Type -> Annotated Type) -> Maybe (Annotated Type) -> (InstanceOrigin, Instance)
      deduce mkConstraint arg' = case (arg, arg') of
        (Nothing, Nothing)    -> (Trivial, IsInstanceOnlyIf [ mkConstraint conType | (_ :< DataCon _ conType) <- alts ])
        (Just arg, Just arg') -> (Trivial, IsInstanceOnlyIf [ mkConstraint (sub (embedSub f) conType) | (_ :< DataCon _ conType) <- alts ]) where
          f :: Annotated Type -> Maybe (Annotated Type)
          f (_ :< t) = case t of
            TyVar n                   -> n `lookup` specialisedVars
            TyView (_ :< ViewVar _ n) -> n `lookup` specialisedVars
            _                         -> Nothing
          specialisedVars = bindTyPat arg arg' where
            bindTyPat :: Annotated TyPat -> Annotated Type -> [(Name, Annotated Type)]
            bindTyPat (_ :< TyPatPack p1 p2) (_ :< TyPack t1 t2) = bindTyPat p1 t1 ++ bindTyPat p2 t2
            bindTyPat (_ :< TyPatVar n) t = [(n, t)]
            bindTyPat (_ :< TyPatViewVar _ n) t = [(n, t)]

      instances = case mode of
        DataUnboxed -> Map.fromList
          [ ("Clone",          deduce clone)
          , ("Dispose",        deduce dispose)
          , ("Copy",           deduce copy)
          ]
        _ -> Map.fromList
          [ ("Clone",          deduce clone)
          , ("Dispose",        deduce dispose)
          ]

    iEnv %= Env.intro name instances
    return $ (src, Just k) :< DeclTypeData mode name arg alts

  DeclTypeEnum name alts -> do
    let k = phantom KindType
    introKind src name k
    let
      instances = Map.fromList
        [ ("Clone",          \Nothing -> (Trivial, IsInstance))
        , ("Dispose",        \Nothing -> (Trivial, IsInstance))
        , ("Copy",           \Nothing -> (Trivial, IsInstance))
        ]
    iEnv %= Env.intro name instances
    return $ (src, Just k) :< DeclTypeEnum name alts


generateDecl :: Annotated Decl -> Praxis (Annotated Decl)
generateDecl (a@(src, _) :< decl) = (a :<) <$> case decl of

  DeclType ty -> DeclType <$> generateDeclType ty

  decl        -> recurseTerm generate decl
