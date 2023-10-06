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
run x = save stage $ do
  stage .= KindCheck Generate
  x' <- generate x
  display x' `ifFlag` debug
  cs <- use (our . constraints)
  display (separate "\n\n" (nub . sort $ cs)) `ifFlag` debug
  return x'

-- TODO since we ignore annotation of input, could adjust this...
generate :: forall a. Term a => Annotated a -> Praxis (Annotated a)
generate x = ($ x) $ case witness :: I a of
  IDecl    -> decl
  IType    -> ty
  ITyOp    -> tyOp
  ITyPat   -> tyPat
  IQTyVar  -> qTyVar
  IDataCon -> dataCon
  _        -> value (recurse generate)

introKind :: Source -> Name -> Annotated Kind -> Praxis ()
introKind s n k = do
  l <- use kEnv
  case lookup n l of
    Just _ -> throwAt s $ "type " <> quote (pretty n) <> " redeclared (in the same scope)"
    _      -> kEnv %= intro n k


qTyVar :: Annotated QTyVar -> Praxis (Annotated QTyVar)
qTyVar = splitTrivial $ \s -> \case

  QTyVar n -> do
    k <- freshKindUni
    introKind s n k
    return (QTyVar n)

  QTyOpVar d n -> do
    introKind s n undefined -- Note: The kind doesn't matter here, just introducting for in-scope checking.
    return (QTyOpVar d n)


tyOp :: Annotated TyOp -> Praxis (Annotated TyOp)
tyOp = splitTrivial $ \s -> \case

  op@(TyOpVar _ n) -> do
    e <- kEnv `uses` lookup n
    case e of
      Just k  -> return op
      Nothing -> throwAt s (NotInScope n)

  op -> return op


ty :: Annotated Type -> Praxis (Annotated Type)
ty = split $ \s -> \case

    TyApply f a -> do
      f' <- ty f
      a' <- ty a
      case view kind f' of
        (_ :< KindOp) -> do
          require $ newConstraint (view kind a' `KEq` phantom KindType) TyOpApplication s
          return (phantom KindType :< TyApply f' a')
        fk -> do
          k <- freshKindUni
          require $ newConstraint (fk `KEq` phantom (KindFun (view kind a') k)) TyFunApplication s
          return (k :< TyApply f' a')

    TyCon n -> do
      e <- kEnv `uses` lookup n
      case e of
        Just k  -> return (k :< TyCon n)
        Nothing -> throwAt s (NotInScope n)

    TyFun a b -> do
      a' <- ty a
      b' <- ty b
      require $ newConstraint (view kind a' `KEq` phantom KindType) FunType s
      require $ newConstraint (view kind b' `KEq` phantom KindType) FunType s
      return (phantom KindType :< TyFun a' b')

    TyOp op -> do
      op' <- tyOp op
      return (phantom KindOp :< TyOp op')

    TyPair p q -> do
      p' <- ty p
      q' <- ty q
      requires $ map (\t -> newConstraint (view kind t `KEq` phantom KindType) PairType s) [p', q']
      return (phantom KindType :< TyPair p' q')

    TyPack p q -> do
      p' <- ty p
      q' <- ty q
      return (phantom (KindPair (view kind p') (view kind q')) :< TyPack p' q')

    TyUnit -> do
      return (phantom KindType :< TyUnit)

    TyVar v -> do
      e <- kEnv `uses` lookup v
      case e of
        Just k  -> return (k :< TyVar v)
        Nothing -> throwAt s (NotInScope v)


tyPat :: Annotated TyPat -> Praxis (Annotated TyPat)
tyPat = split $ \s -> \case

  TyPatVar v -> do
    k <- freshKindUni
    introKind s v k
    return (k :< TyPatVar v)

  TyPatPack a b -> do
    a' <- tyPat a
    b' <- tyPat b
    return (phantom (KindPair (view kind a') (view kind b')) :< TyPatPack a' b')


dataCon :: Annotated DataCon -> Praxis (Annotated DataCon)
dataCon = splitTrivial $ \s -> \case

  DataCon n at -> do
    case at of
      Nothing -> return $ DataCon n Nothing
      Just at -> do
        at' <- generate at
        require $ newConstraint (view kind at' `KEq` phantom KindType) (DataConType n) s -- TODO should just match kind of data type?
        return $ DataCon n (Just at')


fun :: Annotated Kind -> Annotated Kind -> Annotated Kind
fun a b = phantom (KindFun a b)

decl :: Annotated Decl -> Praxis (Annotated Decl)
decl = splitTrivial $ \s -> \case

  -- TODO check no duplicated patterns
  DeclData n ps as -> do
    k <- freshKindUni
    introKind s n k
    (ps', as') <- save kEnv $ do
        ps' <- traverse generate ps
        as' <- traverse generate as
        return (ps', as')
    case ps' of
      Nothing  -> require $ newConstraint (k `KEq` phantom KindType) (DataType n) s
      Just ps' -> require $ newConstraint (k `KEq` phantom (KindFun (view kind ps') (phantom KindType))) (DataType n) s
    return $ DeclData n ps' as'

  x -> recurse generate x

