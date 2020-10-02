{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}

module Check.Kind.Generate
  ( generate
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

generate :: Term a => Annotated a -> Praxis (Annotated a)
generate x = save stage $ do
  stage .= KindCheck Generate
  x' <- generateImpl x
  display x' `ifFlag` debug
  cs <- use (our . constraints)
  display (separate "\n\n" (nub . sort $ cs)) `ifFlag` debug
  return x'

-- TODO since we ignore annotation of input, could adjust this...
generateImpl :: forall a. Term a => Annotated a -> Praxis (Annotated a)
generateImpl x = case witness :: I a of
  IDecl -> decl x
  IType -> ty x
  _     -> value (recurse generateImpl) x

ty :: Annotated Type -> Praxis (Annotated Type)
ty = split $ \s -> \case

    TyApply f a -> do
      k <- freshKindUni
      f' <- ty f
      a' <- ty a
      require $ newConstraint (view kind f' `KEq` phantom (KindFun (view kind a') k)) AppType s
      return (k :< TyApply f' a')

    TyCon n -> do
      e <- kEnv `uses` lookup n
      case e of Nothing -> throwAt s (NotInScope n)
                Just k  -> return (k :< TyCon n)

    TyFun a b -> do
      a' <- ty a
      b' <- ty b
      require $ newConstraint (view kind a' `KEq` phantom KindType) (Custom "typ: TyFun TODO") s
      require $ newConstraint (view kind b' `KEq` phantom KindType) (Custom "typ: TyFun TODO") s
      return (phantom KindType :< TyFun a' b')

    TyOp op t -> do
      t' <- ty t
      require $ newConstraint (view kind t' `KEq` phantom KindType) (Custom "typ: TyOp TODO") s
      return (phantom KindType :< TyOp op t')

    TyPair p q -> do
      p' <- ty p
      q' <- ty q
      requires $ map (\t -> newConstraint (view kind t `KEq` phantom KindType) (Custom "typ: TyPair TODO") s) [p', q']
      return (phantom KindType :< TyPair p' q')

    TyUnit -> do
      return (phantom KindType :< TyUnit)

    TyVar v -> do
      e <- kEnv `uses` lookup v
      case e of
        Just k -> return (k :< TyVar v)
        Nothing -> do
          k <- freshKindUni
          kEnv %= intro v k
          return (k :< TyVar v)


tyPat :: Annotated TyPat -> Praxis (Int, Annotated TyPat)
tyPat = splitPair $ \s -> \case

  TyPatVar v -> do
    e <- kEnv `uses` lookup v
    case e of
      Just k  -> return (1, k :< TyPatVar v)
      Nothing -> do
        k <- freshKindUni
        kEnv %= intro v k
        return (1, k :< TyPatVar v)


dataAlt :: Annotated DataAlt -> Praxis (Annotated DataAlt)
dataAlt = splitTrivial $ \s -> \case

  DataAlt n at -> do
    case at of
      Nothing -> return $ DataAlt n Nothing
      Just at -> do
        at' <- ty at
        require $ newConstraint (view kind at' `KEq` phantom KindType) (Custom "dataAlt: TODO") s
        return $ DataAlt n (Just at')


fun :: Annotated Kind -> Annotated Kind -> Annotated Kind
fun a b = phantom (KindFun a b)

decl :: Annotated Decl -> Praxis (Annotated Decl)
decl = splitTrivial $ \s -> \case

  -- TODO check no duplicated patterns
  DeclData n ps as -> do
    e <- kEnv `uses` lookup n
    case e of
      Just _  -> throwAt s $ "data declaration " <> quote (pretty n) <> " redefined"
      Nothing -> pure ()
    k <- freshKindUni
    kEnv %= intro n k
    (Sum i, ps') <- traverse (over first Sum) <$> traverse tyPat ps
    as' <- traverse dataAlt as
    kEnv %= elimN i
    require $ newConstraint (k `KEq` foldr fun (phantom KindType) (map (view kind) ps')) (Custom "decl: TODO") s
    return $ DeclData n ps' as'

  x -> recurse generateImpl x

