{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
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
import           Pretty
import           Print
import qualified Record
import           Stage
import           Term

import           Data.List          (nub, sort)
import qualified Data.Set           as Set
import           Prelude            hiding (lookup)

kind :: (Recursive a, Functor f, Annotation a ~ Annotated Kind) => (Annotated Kind -> f (Annotated Kind)) -> Annotated a -> f (Annotated a)
kind = annotation . just

generate :: Recursive a => Annotated a -> Praxis (Annotated a)
generate x = save stage $ do
  stage .= KindCheck Generate
  x' <- generateImpl x
  output x'
  cs <- use (our . constraints)
  output $ separate "\n\n" (nub . sort $ cs)
  return x'

-- TODO since we ignore annotation of input, could adjust this...
generateImpl :: Recursive a => Annotated a -> Praxis (Annotated a)
generateImpl x = case typeof x of
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

    TyOp op t -> do
      t' <- ty t
      require $ newConstraint (view kind t' `KEq` phantom KindType) (Custom "typ: TyOp TODO") s
      return (phantom KindType :< TyOp op t')

    TyFun a b -> do
      a' <- ty a
      b' <- ty b
      require $ newConstraint (view kind a' `KEq` phantom KindType) (Custom "typ: TyFun TODO") s
      require $ newConstraint (view kind b' `KEq` phantom KindType) (Custom "typ: TyFun TODO") s
      return (phantom KindType :< TyFun a' b')

    TyFlat ts -> do
      ts' <- traverse ty (Set.toList ts)
      requires $ map (\t -> newConstraint (view kind t `KEq` (phantom KindConstraint)) (Custom "typ: TyFlat TODO") s) ts'
      return (phantom KindConstraint :< TyFlat (Set.fromList ts'))

    TyCon n -> do
      e <- kEnv `uses` lookup n
      case e of Nothing -> throwAt s (NotInScope n)
                Just k  -> return (k :< TyCon n)

    TyRecord r -> do
      r' <- traverse ty r
      requires $ map (\t -> newConstraint (view kind t `KEq` phantom KindType) (Custom "typ: TyRecord TODO") s) (map snd (Record.toList r'))
      return (phantom KindType :< TyRecord r')

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

  DataAlt n ts -> do
    ts' <- traverse ty ts
    requires $ map (\t -> newConstraint (view kind t `KEq` phantom KindType) (Custom "dataAlt: TODO") s) ts'
    return $ DataAlt n ts'


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

