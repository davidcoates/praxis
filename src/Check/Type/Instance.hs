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
      IsInstance           -> return Yes
      IsInstanceOnlyIf tys -> conjunction (map isInstance tys)
    Nothing                -> return No

isInstance :: Annotated Type -> Praxis Truth
isInstance constraint = do
  assumptions' <- use (tySystem . assumptions)
  let
    inst    = Instance constraint
    notInst = Not (phantom inst)
  case (inst `Set.member` assumptions', notInst `Set.member` assumptions') of
    (True, False) -> return Yes
    (False, True) -> return No
    (False, False) -> do
      truth <- isInstance' constraint
      case truth of
        Yes   -> tySystem . assumptions %= Set.insert inst
        No    -> tySystem . assumptions %= Set.insert notInst
        Maybe -> pure ()
      return truth

mkConstraint :: Name -> Annotated Type -> Annotated Type
mkConstraint cls t = phantom (TyApply (phantom (TyCon cls)) t)

isInstance' :: Annotated Type -> Praxis Truth
isInstance' constraint@(_ :< TyApply (_ :< TyCon cls) t) = case view value t of
  TyApply (_ :< TyCon n) t -> isTyConInstance cls n (Just t)
  TyCon n                  -> isTyConInstance cls n Nothing
  TyVar _                  -> return No
  _ | cls `elem` ["Copy", "Clone", "Dispose"] -> case view value t of
    TyUnit                                       -> return Yes
    TyFun _ _                                    -> return Yes
    TyPair a b                                   -> conjunction [isInstance (mkConstraint cls a), isInstance (mkConstraint cls b)]
    TyApply (_ :< TyView (_ :< ViewRef _))   _   -> return Yes
    TyApply (_ :< TyView (_ :< ViewUni Ref _)) _ -> return Yes
    TyApply (_ :< TyView (_ :< ViewVar Ref _)) _ -> return Yes
    TyApply (_ :< TyView (_ :< ViewVar _ _)) a   -> isInstance (mkConstraint cls a)
    _                                            -> return Maybe
  _ | cls `elem` ["CloneTrivial", "DisposeTrivial"] -> case view value t of
      TyUnit                                       -> return Yes
      TyFun _ _                                    -> return No -- !
      TyPair a b                                   -> conjunction [isInstance (mkConstraint cls a), isInstance (mkConstraint cls b)]
      TyApply (_ :< TyView (_ :< ViewRef _))   _   -> return Yes
      TyApply (_ :< TyView (_ :< ViewUni Ref _)) _ -> return Yes
      TyApply (_ :< TyView (_ :< ViewVar Ref _)) _ -> return Yes
      TyApply (_ :< TyView (_ :< ViewVar _ _)) a   -> isInstance (mkConstraint cls a)
      _                                            -> return Maybe
  TyApply (_ :< TyView (_ :< ViewRef _))   _   -> return No
  TyApply (_ :< TyView (_ :< ViewUni Ref _)) _ -> return No
  TyApply (_ :< TyView (_ :< ViewVar _ _)) _   -> return No
  _                                            -> return Maybe

canCopy :: Annotated Type -> Praxis Truth
canCopy t = isInstance (mkConstraint "Copy" t)
