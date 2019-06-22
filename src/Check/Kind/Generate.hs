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
import           Env.KEnv
import           Introspect
import           Praxis
import           Print
import qualified Record
import           Stage
import           Term

import           Data.List          (nub, sort)
import qualified Data.Set           as Set
import           Prelude            hiding (lookup)

kind :: Annotated a b -> Annotation a b
kind = view annotation

generate :: Recursive a => Simple a -> Praxis (Kinded a)
generate x = save stage $ do
  stage .= KindCheck Generate
  x' <- visit gen x
  output x'
  cs <- use (our . constraints)
  output $ separate "\n\n" (nub . sort $ cs)
  return x'

gen :: Recursive a => Simple a -> Visit Praxis (Annotation KindAnn a) (Kinded a)
gen x = case typeof x of
  IDecl    -> case runPraxisT (decl x) of { Nothing -> skip; Just r -> Resolve r }
  IExp     -> skip
  IPat     -> skip
  IProgram -> skip
  IQType   -> skip
  IStmt    -> skip
  IType    -> Resolve (ty x)

ty :: Simple Type -> Praxis (Kinded Type)
ty = split $ \s -> \case

    TyApply f a -> do
      k <- freshUniK
      f' <- ty f
      a' <- ty a
      require $ newConstraint (kind f' `KEq` phantom (KindFun (kind a') k)) AppType s
      return (k :< TyApply f' a')

    TyFun a b -> do
      a' <- ty a
      b' <- ty b
      require $ newConstraint (kind a' `KEq` phantom KindType) (Custom "typ: TyFun TODO") s
      require $ newConstraint (kind b' `KEq` phantom KindType) (Custom "typ: TyFun TODO") s
      return (phantom KindType :< TyFun a' b')

    TyFlat ts -> do
      ts' <- traverse ty (Set.toList ts)
      requires $ map (\t -> newConstraint (kind t `KEq` (phantom KindConstraint)) (Custom "typ: TyFlat TODO") s) ts'
      return (phantom KindConstraint :< TyFlat (Set.fromList ts'))

    TyCon n -> do
      e <- lookup n
      case e of Nothing -> throwAt s (NotInScope n)
                Just k  -> return (k :< TyCon n)

    TyRecord r -> do
      r' <- traverse ty r
      requires $ map (\t -> newConstraint (kind t `KEq` phantom KindType) (Custom "typ: TyRecord TODO") s) (map snd (Record.toList r'))
      return (phantom KindType :< TyRecord r')

    TyVar v -> do
      e <- lookup v
      case e of
        Just k -> return (k :< TyVar v)
        Nothing -> do
          k <- freshUniK
          intro v k
          return (k :< TyVar v)

tyPat :: Simple TyPat -> Praxis (Int, Kinded TyPat)
tyPat = splitPair $ \s -> \case

  TyPatVar v -> do
    e <- lookup v
    case e of
      Just k  -> return (1, k :< TyPatVar v)
      Nothing -> do
        k <- freshUniK
        intro v k
        return (1, k :< TyPatVar v)

dataAlt :: Simple DataAlt -> Praxis (Kinded DataAlt)
dataAlt = split $ \s -> \case

  DataAlt n ts -> do
    ts' <- traverse ty ts
    requires $ map (\t -> newConstraint (kind t `KEq` phantom KindType) (Custom "dataAlt: TODO") s) ts'
    return (() :< DataAlt n ts')

fun :: Kinded Kind -> Kinded Kind -> Kinded Kind
fun a b = phantom (KindFun a b)

decl :: Simple Decl -> PraxisT Maybe (Kinded Decl)
decl = split $ \s -> \case

  -- TODO check no duplicated patterns
  DeclData n ps as -> PraxisT . Just $ do
    e <- lookup n
    case e of
      Just _  -> throwAt s $ "data declaration " <> quote (plain n) <> " redefined"
      Nothing -> pure ()
    k <- freshUniK
    intro n k
    (Sum i, ps') <- traverse (over first Sum) <$> traverse tyPat ps
    as' <- traverse dataAlt as
    elimN i
    require $ newConstraint (k `KEq` foldr fun (phantom KindType) (map kind ps')) (Custom "decl: TODO") s
    return (() :< DeclData n ps' as')

  _ -> lift Nothing
