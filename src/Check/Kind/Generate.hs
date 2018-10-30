{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeFamilies           #-}

module Check.Kind.Generate
  (
  ) where

import           Check.Error
import           Check.Generate
import           Check.Kind.Annotate
import           Check.Kind.Constraint
import           Check.Kind.Require
import           Check.Type.Annotate
import           Common
import qualified Env.KEnv              as KEnv
import           Error
import           Introspect
import           Praxis
import qualified Record
import           Source
import           Stage
import           Stage
import           Tag
import           Type

import qualified Data.Set              as Set

kind = view annotation

throwCheckError r = throwError (CheckError r)

instance Recursive a => Generatable TypeCheck KindCheck a where
  generate' = introspect gen

gen :: Recursive a => Annotated TypeCheck a -> Intro Praxis KindCheck a
gen x = case typeof x of
  IDataAlt -> Notice (pure ())
  IDecl    -> Notice (introspect gen (view annotation x))
  IExp     -> Notice (both (introspect gen) (view annotation x))
  IPat     -> Notice (introspect gen (view annotation x))
  IProgram -> Notice (pure ())
  IQType   -> Notice (pure ())
  IStmt    -> Notice (introspect gen (view annotation x))
  IType    -> Realise (genType x)
  -- TODO TyPat?

genType :: Typed Type -> Praxis (Kinded Type)
genType x = let s = view source x in (\(k :< t) -> (s, k) :< t) <$> case view value x of

    TyApply f a -> do
      k <- freshUniK
      f' <- generate' f
      a' <- generate' a
      require $ newConstraint ((kind f') `Eq` KindFun (kind a') k) AppType s
      return (k :< TyApply f' a')

    -- TODO allow constraints here too, not just effects
    TyFlat ts -> do
      ts' <- traverse generate' (Set.toList ts)
      requires $ map (\t -> newConstraint (kind t `Eq` KindEffect) (Custom "typ: TyFlat TODO") s) ts'
      return (KindEffect :< TyFlat (Set.fromList ts'))

    TyCon n -> do
      e <- KEnv.lookup n
      case e of Nothing -> throwCheckError (NotInScope n s)
                Just k  -> return (k :< TyCon n)

    TyPack r -> do -- This one is easy
      r' <- traverse generate' r
      return (KindRecord (fmap kind r') :< TyPack r')

    TyRecord r -> do
      r' <- traverse generate' r
      requires $ map (\t -> newConstraint (kind t `Eq` KindType) (Custom "typ: TyRecord TODO") s) (map snd (Record.toList r'))
      return (KindType :< TyRecord r')

    TyVar v -> do
      e <- KEnv.lookup v
      case e of
        Just k -> return (k :< TyVar v)
        Nothing -> do
          k <- freshUniK
          KEnv.intro v k
          return (k :< TyVar v)

