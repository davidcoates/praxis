{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeFamilies           #-}

module Check.Kind.Generate
  ( generate
  ) where

import           Annotate
import           Check.Error
import           Check.Kind.Reason
import           Check.Kind.Require
import           Common
import qualified Env.KEnv           as KEnv
import           Introspect
import           Kind
import           Praxis
import qualified Record
import           Stage
import           Type               hiding (Constraint (..))

import qualified Data.Set           as Set

kind = view annotation

generate :: Recursive a => Typed a -> Praxis (Kinded a)
generate x = save stage $ do
  stage .= KindCheck Generate
  x' <- introspect gen x
  return x'

gen :: Recursive a => Typed a -> Intro Praxis KindCheck a
gen x = case typeof x of
  IDataAlt -> Notice (pure ())
  IDecl    -> Notice (pure ())
  IExp     -> Notice (introspect gen (view annotation x))
  IPat     -> Notice (introspect gen (view annotation x))
  IProgram -> Notice (pure ())
  IQType   -> Notice (pure ())
  IStmt    -> Notice (pure ())
  IType    -> Realise (ty x)
  -- TODO TyPat?

split :: ((Source, a TypeCheck) -> Praxis (Annotation KindCheck a, a KindCheck)) -> Typed a -> Praxis (Kinded a)
split f x = do
  (a', x') <- f (view source x, view value x)
  return ((view source x, a') :< x')

ty :: Typed Type -> Praxis (Kinded Type)
ty = split $ \(s, t) -> case t of

    TyApply f a -> do
      k <- freshUniK
      f' <- ty f
      a' <- ty a
      require $ newConstraint (kind f' `Eq` ((Phantom, ()) :< KindFun (kind a') k)) AppType s
      return (k, TyApply f' a')

    TyFun a b -> do
      a' <- ty a
      b' <- ty b
      require $ newConstraint (kind a' `Eq` ((Phantom, ()) :< KindType)) (Custom "typ: TyFun TODO") s
      require $ newConstraint (kind b' `Eq` ((Phantom, ()) :< KindType)) (Custom "typ: TyFun TODO") s
      return ((Phantom, ()) :< KindType, TyFun a' b')

    TyFlat ts -> do
      ts' <- traverse ty (Set.toList ts)
      requires $ map (\t -> newConstraint (kind t `Eq` ((Phantom, ()) :< KindConstraint)) (Custom "typ: TyFlat TODO") s) ts'
      return ((Phantom, ()) :< KindConstraint, TyFlat (Set.fromList ts'))

    TyCon n -> do
      e <- KEnv.lookup n
      case e of Nothing -> throw (NotInScope n s)
                Just k  -> return (k, TyCon n)

    TyPack r -> do -- This one is easy
      r' <- traverse ty r
      return ((Phantom, ()) :< KindRecord (fmap kind r'), TyPack r')

    TyRecord r -> do
      r' <- traverse ty r
      requires $ map (\t -> newConstraint (kind t `Eq` ((Phantom, ()) :< KindType)) (Custom "typ: TyRecord TODO") s) (map snd (Record.toList r'))
      return ((Phantom, ()) :< KindType, TyRecord r')

    TyVar v -> do
      e <- KEnv.lookup v
      case e of
        Just k -> return (k, TyVar v)
        Nothing -> do
          k <- freshUniK
          KEnv.intro v k
          return (k, TyVar v)

