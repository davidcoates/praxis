{-# LANGUAGE ImpredicativeTypes   #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Check.Type.Solve
  ( run
  , normalise
  ) where

import           Check.Solve
import           Common
import qualified Env.Env             as Env
import qualified Env.LEnv            as LEnv
import           Introspect
import           Praxis
import           Stage               hiding (Unknown)
import           Term

import           Control.Applicative (liftA2)
import           Data.List           (foldl', nub, sort)
import           Data.Maybe          (fromMaybe)
import           Data.Set            (Set, union)
import qualified Data.Set            as Set
import           Data.Traversable    (forM)


run :: Term a => Annotated a -> Praxis (Annotated a)
run term = do
  term <- solve tySystem reduce term
  tryDefault term

reduce :: Disambiguating (Reducer TyConstraint)
reduce disambiguate = \case

  Copy t -> do
    r <- canCopy t
    return $ case r of
      Yes   -> Tautology
      No    -> Contradiction
      Maybe -> Skip

  TEq t1 t2 | t1 == t2 -> return Tautology

  TEq (_ :< TyUni x) t -> if x `Set.member` tyUnis t then return Contradiction else solved (x `is` view value t) -- Note: Occurs check here

  TEq t1 t2@(_ :< TyUni _) -> reduce disambiguate (t2 `TEq` t1) -- handle by the above case

  TEq (_ :< TyApply (_ :< TyCon n1) t1) (_ :< TyApply (_ :< TyCon n2) t2)
    | n1 == n2 -> return $ Subgoals [ TEq t1 t2 ]
    | otherwise -> return Contradiction

  TEq (_ :< TyPack s1 s2) (_ :< TyPack t1 t2) -> return $ Subgoals [ TEq s1 t1, TEq s2 t2 ]

  TEq (_ :< TyPair s1 s2) (_ :< TyPair t1 t2) -> return $ Subgoals [ TEq s1 t1, TEq s2 t2 ]

  TEq (_ :< TyFun t1 t2) (_ :< TyFun s1 s2) -> return $ Subgoals [ TEq t1 s1, TEq t2 s2 ]

  TEq t1@(_ :< TyApply (_ :< TyView _) t1') t2 -> return $ Subgoals [ TEq (stripOuterViews t1') (stripOuterViews t2), TOpEq t1 t2 ]

  TEq t1 t2@(_ :< TyApply (_:< TyView _) _) -> reduce disambiguate (t2 `TEq` t1) -- handled by the above case

  TOpEq t1 t2 | outerViews t1 == outerViews t2 -> return Tautology

  TOpEq t1 t2 -> do
    r <- canCopy (stripOuterViews t1) -- stripOuterViews t1 == stripOuterViews t2
    case r of
      No -> do
        let (vs1, vs2) = let f = Set.toList . outerViews in (f t1, f t2)
        case (if vs1 < vs2 then (vs1, vs2) else (vs2, vs1)) of
          ([], []) -> return Tautology
          ([], vs) -> do
            if all (\v -> case view value v of { ViewUni RefOrValue _ -> True; _ -> False }) vs
              then solved (areViews (map (\(_ :< ViewUni _ n) -> (n, ViewValue)) vs))
              else return Contradiction
          -- TODO do we need occurs checks here?
          ([_ :< v@(ViewUni _ _)], [_ :< ViewUni _ n])        -> solved (n `isView` v) -- Note: Ref < RefOrValue (i.e. restrain the more general one)
          ([_ :< ViewUni RefOrValue n], [_ :< v])             -> solved (n `isView` v)
          ([_ :< ViewUni Ref n], [_ :< ViewValue])            -> return Contradiction
          ([_ :< ViewUni Ref n], [_ :< ViewVar RefOrValue _]) -> return Contradiction
          ([_ :< ViewUni Ref n], [_ :< v@(ViewVar Ref _)])    -> solved (n `isView` v)
          ([_ :< ViewUni Ref n], [_ :< v@(ViewRef _)])        -> solved (n `isView` v)
          _ -> return Skip
      _ -> return Skip

  RefFree refName t
    | refName `Set.member` viewRefs t
      -> return Contradiction
    | Set.null (tyUnis t) && Set.null (viewUnis t)
      -> return Tautology
    | otherwise
      -> return Skip

  Class (_ :< cls) | disambiguate -> case cls of
    TyApply (_ :< TyCon "Integral") t
      -> return $ Subgoals [ TEq t (TyCon "I32" `as` phantom KindType) ]
    _
      -> return Contradiction

  Class _ | not disambiguate -> return Skip -- TODO

  _ -> return Contradiction


  where
    tyUnis :: forall a. Term a => Annotated a -> Set Name
    tyUnis = extract (embedMonoid f) where
      f = \case
        TyUni n -> Set.singleton n
        _       -> Set.empty

    viewUnis :: forall a. Term a => Annotated a -> Set Name
    viewUnis = extract (embedMonoid f) where
      f = \case
        ViewUni _ n -> Set.singleton n
        _           -> Set.empty

    viewRefs :: forall a. Term a => Annotated a -> Set Name
    viewRefs = extract (embedMonoid f) where
      f = \case
        ViewRef n -> Set.singleton n
        _         -> Set.empty

    outerViews :: Annotated Type -> Set (Annotated View)
    outerViews ty = case view value ty of
      TyApply (_ :< TyView v) ty -> Set.insert v (outerViews ty)
      _                          -> Set.empty


-- Rewrite helpers
solved :: Resolver -> Praxis (Reduction TyConstraint)
solved resolve = do
  tEnv %%= traverse (LEnv.value (normalise . sub resolve))
  return (Solved (resolve, normalise))

isView :: Name -> View -> Resolver
isView n v = embedSub f where
  f (a :< x) = case x of
    ViewUni _ n' -> if n == n' then Just (a :< v) else Nothing
    _            -> Nothing

areViews :: [(Name, View)] -> Resolver
areViews vs = embedSub f where
  f (a :< x) = case x of
    ViewUni _ n -> case n `lookup` vs of { Just v -> Just (a :< v); Nothing -> Nothing }
    _           -> Nothing

is :: Name -> Type -> Resolver
is n t = embedSub f where
  f (a :< x) = case x of
    TyUni n' -> if n == n' then Just (a :< t) else Nothing
    _        -> Nothing


-- View helpers
stripOuterViews :: Annotated Type -> Annotated Type
stripOuterViews ty = case view value ty of
  TyApply (_ :< TyView _) ty -> stripOuterViews ty
  _                          -> ty

simplifyOuterViews :: Annotated Type -> Annotated Type
simplifyOuterViews = simplifyOuterViews' [] where

  simplifyOuterViews' :: [View] -> Annotated Type -> Annotated Type
  simplifyOuterViews' vs (a :< ty) = case ty of

    TyApply f@(_ :< TyView (_ :< v)) innerTy -> case v of

      ViewValue -> simplifyOuterViews' vs innerTy

      _

        | v `elem` vs -> simplifyOuterViews' vs innerTy

        | otherwise   -> a :< TyApply f (simplifyOuterViews' (v:vs) innerTy)

    _ -> a :< ty


-- Term normaliser (after a substitution is applied)
normalise :: Normaliser
normalise (a :< x) = case typeof x of

  IType -> case x of

    TyApply (_ :< TyView _) _ -> case simplifyOuterViews (a :< x) of

      ty@(_ :< TyApply (_ :< TyView _) innerTy) -> do
        -- The view can be safely stripped if the /* stripped */ type is copyable.
        --
        -- E.g. we can not strip &a from &a &b List Int (because List Int is not copyable)
        -- But we can strip &a from &a &b Int, and then &b from &b Int.
        canStripOps <- canCopy (stripOuterViews innerTy)
        case canStripOps of
          Yes -> normalise (stripOuterViews innerTy)
          _   -> return ty

      ty -> return ty

    _ -> continue

  _ -> continue

  where continue = recurse normalise (a :< x)


-- Copy helpers
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

canCopyTyCon :: Name -> Maybe (Annotated Type) -> Praxis Truth
canCopyTyCon name arg = do
  l <- use dtEnv
  let Just checkCanCopy = Env.lookup name l
  case checkCanCopy arg of
    CanCopy           -> return Yes
    CanNotCopy        -> return No
    CanCopyOnlyIf tys -> conjunction (map canCopy tys)

canCopy :: Annotated Type -> Praxis Truth
canCopy t = do
  assumptions' <- use (tySystem . assumptions)
  case (Copy t `Set.member` assumptions', NoCopy t `Set.member` assumptions') of
    (True, False) -> return Yes
    (False, True) -> return No
    (False, False) -> do
      truth <- canCopy'
      case truth of
        Yes   -> tySystem . assumptions %= Set.insert (Copy t)
        No    -> tySystem . assumptions %= Set.insert (NoCopy t)
        Maybe -> pure ()
      return truth
  where
    canCopy' = case view value t of
      TyUnit                                       -> return Yes
      TyFun _ _                                    -> return Yes
      TyPair a b                                   -> conjunction [canCopy a, canCopy b]
      TyVar _                                      -> return No
      TyCon n                                      -> canCopyTyCon n Nothing
      TyApply (_ :< TyCon n) t                     -> canCopyTyCon n (Just t)
      TyApply (_ :< TyView (_ :< ViewRef _))   _   -> return Yes
      TyApply (_ :< TyView (_ :< ViewUni Ref _)) _ -> return Yes
      TyApply (_ :< TyView (_ :< ViewVar Ref _)) _ -> return Yes
      TyApply (_ :< TyView (_ :< ViewVar _ _)) a   -> canCopy a
      TyApply (_ :< TyView (_ :< ViewValue)) a     -> canCopy a
      _                                            -> return Maybe


-- Check for undetermined unification variables, default them where possible
tryDefault :: Term a => Annotated a -> Praxis (Annotated a)
tryDefault term@((src, _) :< _) = do

  -- TODO could just be a warning, and default to ()?
  let freeTys = deepTyUnis term
  when (not (null freeTys)) $ throwAt src $ "underdetermined type: " <> quote (pretty (Set.elemAt 0 freeTys))

  let
    defaultView name = do
      warnAt src $ "underdetermined view: " <> quote (pretty name) <> ", defaulting to &"
      v <- freshViewRef
      return (name, view value v)

    freeViews = deepViewUnis term

  defaultViews <- mapM defaultView (Set.toList freeViews)

  case defaultViews of
    [] -> return term
    _  -> do
      Solved (resolve, normalise) <- solved (areViews defaultViews)
      (normalise . sub resolve) term

  where
    deepTyUnis :: forall a. Term a => Annotated a -> Set Name
    deepTyUnis = deepExtract (embedMonoid f) where
      f = \case
        TyUni n -> Set.singleton n
        _       -> Set.empty

    deepViewUnis :: forall a. Term a => Annotated a -> Set Name
    deepViewUnis = deepExtract (embedMonoid f) where
      f = \case
        ViewUni _ n -> Set.singleton n
        _           -> Set.empty

