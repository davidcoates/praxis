{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeFamilies           #-}

module Check.Kind.Generate
  ( generate
  ) where

import           Check.Error
import           Check.Kind.Reason
import           Check.Kind.Require
import           Common
import qualified Env.KEnv           as KEnv
import           Introspect
import           Praxis
import qualified Record
import           Stage
import           Term

import qualified Data.Set           as Set

kind = view annotation

generate :: Recursive a => Simple a -> Praxis (Kinded a)
generate x = save stage $ do
  stage .= KindCheck Generate
  x' <- visit gen x
  return x'

gen :: Recursive a => Simple a -> Visit Praxis (Annotation KindAnn a) (Kinded a)
gen x = case typeof x of
  IDataAlt -> skip
  IDecl    -> skip -- TODO (data alt)
  IExp     -> skip
  IPat     -> skip
  IProgram -> skip
  IQType   -> skip
  IStmt    -> skip
  IType    -> Resolve (ty x)
  ITyPat   -> undefined -- TODO

split :: ((Source, a SimpleAnn) -> Praxis (Annotation KindAnn a, a KindAnn)) -> Simple a -> Praxis (Kinded a)
split f x = do
  (a', x') <- f (view source x, view value x)
  return ((view source x, a') :< x')

ty :: Simple Type -> Praxis (Kinded Type)
ty = split $ \(s, t) -> case t of

    TyApply f a -> do
      k <- freshUniK
      f' <- ty f
      a' <- ty a
      require $ newConstraint (kind f' `KEq` phantom (KindFun (kind a') k)) AppType s
      return (k, TyApply f' a')

    TyFun a b -> do
      a' <- ty a
      b' <- ty b
      require $ newConstraint (kind a' `KEq` phantom KindType) (Custom "typ: TyFun TODO") s
      require $ newConstraint (kind b' `KEq` phantom KindType) (Custom "typ: TyFun TODO") s
      return (phantom KindType, TyFun a' b')

    TyFlat ts -> do
      ts' <- traverse ty (Set.toList ts)
      requires $ map (\t -> newConstraint (kind t `KEq` (phantom KindConstraint)) (Custom "typ: TyFlat TODO") s) ts'
      return (phantom KindConstraint, TyFlat (Set.fromList ts'))

    TyCon n -> do
      e <- KEnv.lookup n
      case e of Nothing -> throwAt s (NotInScope n)
                Just k  -> return (k, TyCon n)

    TyPack r -> do -- This one is easy
      r' <- traverse ty r
      return (phantom $ KindRecord (fmap kind r'), TyPack r')

    TyRecord r -> do
      r' <- traverse ty r
      requires $ map (\t -> newConstraint (kind t `KEq` phantom KindType) (Custom "typ: TyRecord TODO") s) (map snd (Record.toList r'))
      return (phantom KindType, TyRecord r')

    TyVar v -> do
      e <- KEnv.lookup v
      case e of
        Just k -> return (k, TyVar v)
        Nothing -> do
          k <- freshUniK
          KEnv.intro v k
          return (k, TyVar v)

