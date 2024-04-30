
module Check.Type.Instance
  ( Truth(..)
  , isInstance
  , canCopy
  ) where

import           Common
import qualified Env.Env         as Env
import           Inbuilts        (copy)
import           Praxis
import           Term

import qualified Data.Map.Strict as Map
import           Data.Set        (Set)
import qualified Data.Set        as Set


data Truth = Yes | No | Maybe
  deriving Eq

conjunction :: [Praxis Truth] -> Praxis Truth
conjunction = conjunction' Yes where
  conjunction' :: Truth -> [Praxis Truth] -> Praxis Truth
  conjunction' t1 [] = return t1
  conjunction' t1 (t2:ts) = do
    t2 <- t2
    case t2 of
      Yes   -> conjunction' t1 ts
      No    -> return No
      Maybe -> conjunction' Maybe ts

isTyConInstance :: Name -> Name -> Maybe (Annotated Type) -> Praxis Truth
isTyConInstance cls name arg = do
  l <- use iEnv
  let Just instances = Env.lookup name l
  case Map.lookup cls instances of
    Just resolver -> case resolver arg of
      (_, IsInstance)           -> return Yes
      (_, IsInstanceOnlyIf tys) -> conjunction (map isInstance tys)
    Nothing                     -> return No

isInstance :: Annotated Type -> Praxis Truth
isInstance inst@(_ :< TyApply (_ :< TyCon n) t) = do
  assumptions' <- use (tySystem . assumptions)
  case (Instance inst `Set.member` assumptions', Not (phantom (Instance inst)) `Set.member` assumptions') of
    (True, False) -> return Yes
    (False, True) -> return No
    (False, False) -> do
      truth <- isInstance'
      case truth of
        Yes   -> tySystem . assumptions %= Set.insert (Instance inst)
        No    -> tySystem . assumptions %= Set.insert (Not (phantom (Instance inst)))
        Maybe -> pure ()
      return truth
  where
    isInstance' = case n of
      "Copy"    -> canCopy t
      "Clone"   -> canClone t
      "Dispose" -> return Yes
      cls       -> case view value t of
        TyApply (_ :< TyCon n) t -> isTyConInstance cls n (Just t)
        TyCon n                  -> isTyConInstance cls n Nothing
        _                        -> return Maybe

canClone :: Annotated Type -> Praxis Truth
canClone t = undefined

canDispose :: Annotated Type -> Praxis Truth
canDispose t = undefined

canCopy :: Annotated Type -> Praxis Truth
canCopy t = case view value t of
  TyUnit                                       -> return Yes
  TyFun _ _                                    -> return Yes
  TyPair a b                                   -> conjunction [isInstance (copy a), isInstance (copy b)]
  TyVar _                                      -> return No
  TyCon n                                      -> isTyConInstance "Copy" n Nothing
  TyApply (_ :< TyCon n) t                     -> isTyConInstance "Copy" n (Just t)
  TyApply (_ :< TyView (_ :< ViewRef _))   _   -> return Yes
  TyApply (_ :< TyView (_ :< ViewUni Ref _)) _ -> return Yes
  TyApply (_ :< TyView (_ :< ViewVar Ref _)) _ -> return Yes
  TyApply (_ :< TyView (_ :< ViewVar _ _)) a   -> isInstance (copy a)
  TyApply (_ :< TyView (_ :< ViewValue)) a     -> isInstance (copy a)
  _                                            -> return Maybe
