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

import           Check.Error
import           Check.Kind.Reason
import           Check.Kind.Require
import           Check.Kind.System
import           Common
import           Env
import           Introspect
import           Praxis
import           Print
import           Stage
import           Term

import           Data.List          (nub, sort)
import qualified Data.Set           as Set
import           Prelude            hiding (lookup)

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
generate :: forall a. Term a => Annotated a -> Praxis (Annotated a)
generate term = ($ term) $ case witness :: I a of
  IDecl    -> generateDecl
  IType    -> generateTy
  ITyOp    -> generateTyOp
  ITyPat   -> generateTyPat
  IQTyVar  -> generateQTyVar
  IDataCon -> generateDataCon
  _        -> value (recurse generate)

introKind :: Source -> Name -> Annotated Kind -> Praxis ()
introKind s n k = do
  l <- use kEnv
  case lookup n l of
    Just _ -> throwAt s $ "type " <> quote (pretty n) <> " redeclared (in the same scope)"
    _      -> kEnv %= intro n k


generateQTyVar :: Annotated QTyVar -> Praxis (Annotated QTyVar)
generateQTyVar = splitTrivial $ \src -> \case

  QTyVar var -> do
    k <- freshKindUni
    introKind src var k
    return (QTyVar var)

  QTyOpVar domain var -> do
    introKind src var undefined -- Note: The kind doesn't matter here, just introducting for in-scope checking.
    return (QTyOpVar domain var)


generateTyOp :: Annotated TyOp -> Praxis (Annotated TyOp)
generateTyOp = splitTrivial $ \src -> \case

  op@(TyOpVar _ var) -> do
    entry <- kEnv `uses` lookup var
    case entry of
      Just _  -> return op
      Nothing -> throwAt src (NotInScope var)

  op -> return op


generateTy :: Annotated Type -> Praxis (Annotated Type)
generateTy = split $ \src -> \case

    TyApply f x -> do
      f <- generateTy f
      x <- generateTy x
      case view kind f of
        (_ :< KindOp) -> do
          require $ newConstraint (view kind x `KEq` phantom KindType) TyOpApplication src
          return (phantom KindType :< TyApply f x)
        funKind -> do
          k <- freshKindUni
          require $ newConstraint (funKind `KEq` phantom (KindFun (view kind x) k)) TyFunApplication src
          return (k :< TyApply f x)

    TyCon con -> do
      entry <- kEnv `uses` lookup con
      case entry of
        Just k  -> return (k :< TyCon con)
        Nothing -> throwAt src (NotInScope con)

    TyFun ty1 ty2 -> do
      ty1 <- generateTy ty1
      ty2 <- generateTy ty2
      require $ newConstraint (view kind ty1 `KEq` phantom KindType) FunType src
      require $ newConstraint (view kind ty2 `KEq` phantom KindType) FunType src
      return (phantom KindType :< TyFun ty1 ty2)

    TyOp op -> do
      op <- generateTyOp op
      return (phantom KindOp :< TyOp op)

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
      entry <- kEnv `uses` lookup var
      case entry of
        Just k  -> return (k :< TyVar var)
        Nothing -> throwAt src (NotInScope var)


generateTyPat :: Annotated TyPat -> Praxis (Annotated TyPat)
generateTyPat = split $ \src -> \case

  TyPatVar var -> do
    k <- freshKindUni
    introKind src var k
    return (k :< TyPatVar var)

  TyPatPack tyPat1 tyPat2 -> do
    tyPat1 <- generateTyPat tyPat1
    tyPat2 <- generateTyPat tyPat2
    return (phantom (KindPair (view kind tyPat1) (view kind tyPat2)) :< TyPatPack tyPat1 tyPat2)


generateDataCon :: Annotated DataCon -> Praxis (Annotated DataCon)
generateDataCon = splitTrivial $ \src -> \case

  DataCon name arg -> do
    case arg of
      Nothing -> return $ DataCon name Nothing
      Just arg -> do
        arg <- generate arg
        require $ newConstraint (view kind arg `KEq` phantom KindType) (DataConType name) src -- TODO should just match kind of data type?
        return $ DataCon name (Just arg)


fun :: Annotated Kind -> Annotated Kind -> Annotated Kind
fun a b = phantom (KindFun a b)

generateDecl :: Annotated Decl -> Praxis (Annotated Decl)
generateDecl = splitTrivial $ \src -> \case

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

  decl -> recurse generate decl
