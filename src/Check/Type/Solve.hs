{-# LANGUAGE ImpredicativeTypes   #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Check.Type.Solve
  ( assumeFromQType
  , run
  , normalise
  ) where

import           Check.Solve
import           Check.State
import           Common
import qualified Env.Linear          as LEnv
import qualified Env.Strict          as Env
import           Inbuilts            (copy)
import           Introspect
import           Praxis
import           Stage               hiding (Unknown)
import           Term

import           Control.Applicative (liftA2)
import           Data.List           (foldl', nub, sort)
import qualified Data.Map.Strict     as Map
import           Data.Maybe          (fromMaybe)
import           Data.Set            (Set)
import qualified Data.Set            as Set


run :: Term a => Annotated a -> Praxis (Annotated a)
run term = do
  term <- solve tyCheckState reduce term
  tryDefault term

unapplyTyCon :: Annotated Type -> Maybe (Name, [Annotated Type])
unapplyTyCon (_ :< ty) = case ty of
  TyCon n -> Just (n, [])
  TyApply t1 t2 -> case unapplyTyCon t1 of
    Just (n, ts) -> Just (n, ts ++ [t2])
    Nothing      -> Nothing
  _ -> Nothing

reduce :: Disambiguating (Reducer TyConstraint)
reduce disambiguate = \case

  TEq t1 t2 | t1 == t2 -> return Tautology

  TEq (_ :< TyUni x) t -> if x `Set.member` tyUnis t then return Contradiction else solved (x `is` view value t) -- Note: Occurs check here

  TEq t1 t2@(_ :< TyUni _) -> reduce disambiguate (t2 `TEq` t1) -- handle by the above case

  TEq t1 t2
    | (Just (n1, t1s), Just (n2, t2s)) <- (unapplyTyCon t1, unapplyTyCon t2) ->
      if n1 == n2
        then return $ Subgoals (zipWith (\t1 t2 -> Subgoal (TEq t1 t2)) t1s t2s)
        else return Contradiction

  TEq (_ :< TyPair s1 s2) (_ :< TyPair t1 t2) -> return $ Subgoals [ Subgoal (TEq s1 t1), Subgoal (TEq s2 t2) ]

  TEq (_ :< TyFn t1 t2) (_ :< TyFn s1 s2) -> return $ Subgoals [ Subgoal (TEq t1 s1), Subgoal (TEq t2 s2) ]

  TEq t1@(_ :< TyApply (_ :< TyView _) t1') t2 -> return $ Subgoals [ Subgoal (TEq (stripOuterViews t1') (stripOuterViews t2)), Subgoal (TOpEq t1 t2) ]

  TEq t1 t2@(_ :< TyApply (_:< TyView _) _) -> reduce disambiguate (t2 `TEq` t1) -- handled by the above case

  TOpEq t1 t2 | outerViews t1 == outerViews t2 -> return Tautology

  TOpEq t1 t2 -> do
    affine <- isAffine (stripOuterViews t1) -- stripOuterViews t1 == stripOuterViews t2
    case affine of
      No -> return Skip
      Unknown -> return Skip
      _  -> do
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
          ([_ :< ViewUni Ref n], [_ :< ViewValue])            -> error "unnormalised"  -- Sanity check: This is unexpected since t1 and t2 should be normalised
          ([_ :< ViewUni Ref n], [_ :< ViewVar RefOrValue _]) -> return Contradiction
          ([_ :< ViewUni Ref n], [_ :< v@(ViewVar Ref _)])    -> solved (n `isView` v)
          ([_ :< ViewUni Ref n], [_ :< v@(ViewRef _)])        -> solved (n `isView` v)
          _ -> return Skip

  RefFree refName t
    | refName `Set.member` viewRefs t
      -> return Contradiction
    | Set.null (tyUnis t) && Set.null (viewUnis t)
      -> return Tautology
    | otherwise
      -> return Skip

  Instance (a0 :< inst) -> case inst of

    TyApply (_ :< TyCon "Integral") t | disambiguate
      -> return $ Subgoals [ Subgoal (TEq t (TyCon "I32" `as` phantom KindType)) ]

    TyApply (a1 :< TyCon cls) t -> case view value t of
      TyApply tyView@(_ :< TyView (_ :< view)) t -> do
        let
          instVal = Instance (a0 :< TyApply (a1 :< TyCon cls) t)
          instRef = Instance (a0 :< TyApply (a1 :< TyCon cls) (phantom (TyApply (phantom (TyCon "Ref")) t)))
        affine <- isAffine t
        case (isRef view, affine) of
          (No, _)         -> error "unnormalised"
          (_, No)         -> error "unnormalised"
          (_, Unknown)    -> return Skip
          (Unknown, _)    -> return Skip
          (Yes, Yes)      -> reduceTyConInstance cls "Ref" [t]
          (Yes, Variable) -> return $ Subgoals [ Subgoal instRef, copy t `Implies` instVal ]
          (Variable, _)   -> return $ Subgoals [ Subgoal instRef, Subgoal instVal ]
      TyPair t1 t2 -> reduceTyConInstance cls "Pair" [t1, t2]
      TyFn t1 t2 -> reduceTyConInstance cls "Fn" [t1, t2]
      TyUnit -> reduceTyConInstance cls "Unit" []
      TyVar _ -> return Contradiction
      _ | Just (n, ts) <- unapplyTyCon t -> reduceTyConInstance cls n ts
      _ -> return Skip


  HoldsInteger n (_ :< t) -> case t of
    TyCon "I8"    -> checkBounds n (undefined :: I8)
    TyCon "I16"   -> checkBounds n (undefined :: I16)
    TyCon "I32"   -> checkBounds n (undefined :: I32)
    TyCon "I64"   -> checkBounds n (undefined :: I64)
    TyCon "ISize" -> checkBounds n (undefined :: ISize)
    TyCon "U8"    -> checkBounds n (undefined :: U8)
    TyCon "U16"   -> checkBounds n (undefined :: U16)
    TyCon "U32"   -> checkBounds n (undefined :: U32)
    TyCon "U64"   -> checkBounds n (undefined :: U64)
    TyCon "USize" -> checkBounds n (undefined :: USize)
    _             -> return Skip
    where
      checkBounds :: forall a. (Integral a, Bounded a) => Integer -> a -> Praxis (Reduction TyConstraint)
      checkBounds n _ = if toInteger (minBound :: a) <= n && n <= toInteger (maxBound :: a) then return Tautology else return Contradiction

  _ -> return Contradiction


  where
    reduceTyConInstance :: Name -> Name -> [Annotated Type] -> Praxis (Reduction TyConstraint)
    reduceTyConInstance cls name args = do
      l <- use iEnv
      let Just instances = Env.lookup name l
      case Map.lookup cls instances of
        Just resolver -> case resolver args of
          (_, IsInstance)          -> return Tautology
          (_, IsInstanceOnlyIf cs) -> return (Subgoals (map Subgoal cs))
        Nothing                    -> return Contradiction

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

-- Term normaliser (after a substitution is applied)
normalise :: Normaliser
normalise (a :< x) = case typeof x of

  IType -> case x of

    TyApply tyView@(_ :< TyView (_ :< view)) ty -> do
      ty <- normalise ty
      case view of
        ViewValue -> return ty
        _         -> do
          affine <- isAffine ty
          case affine of
            No -> return $ ty
            _  -> return $ (a :< TyApply tyView ty)

    _ -> continue

  _ -> continue

  where
    continue = recurse normalise (a :< x)


data Truth = Yes | No | Variable | Unknown

isRef :: View -> Truth
isRef = \case
  ViewUni Ref _        -> Yes
  ViewUni RefOrValue _ -> Unknown
  ViewRef _            -> Yes
  ViewVar Ref _        -> Yes
  ViewVar RefOrValue _ -> Variable

truthOr :: Truth -> Truth -> Truth
truthOr Yes _      = Yes
truthOr _ Yes      = Yes
truthOr Unknown _  = Unknown
truthOr _ Unknown  = Unknown
truthOr _ Variable = Variable
truthOr Variable _ = Variable
truthOr No No      = No

truthNot :: Truth -> Truth
truthNot Yes      = No
truthNot No       = Yes
truthNot Unknown  = Unknown
truthNot Variable = Variable

truthAnd :: Truth -> Truth -> Truth
truthAnd a b = truthNot (truthOr (truthNot a) (truthNot b))

isAffine :: Annotated Type -> Praxis Truth
isAffine t = do
  assumptions' <- use (tyCheckState . assumptions)
  if copy t `Set.member` assumptions'
    then return No
    else isAffine' t
  where
    isAffine' :: Annotated Type -> Praxis Truth
    isAffine' (a :< t) = case t of
      TyPair t1 t2 -> isTyConAffine "Pair" [t1, t2]
      TyFn t1 t2 -> isTyConAffine "Fn" [t1, t2]
      TyUnit -> isTyConAffine "Unit" []
      TyApply (_ :< TyView (_ :< view)) t -> truthAnd (truthNot (isRef view)) <$> isAffine t
      TyUni _ -> return Unknown
      TyVar _ -> return Variable
      _ | Just (n, ts) <- unapplyTyCon (a :< t) -> isTyConAffine n ts

isTyConAffine :: Name -> [Annotated Type] -> Praxis Truth
isTyConAffine name args = do
  l <- use iEnv
  let Just instances = Env.lookup name l
  case Map.lookup "Copy" instances of
    Just resolver -> case resolver args of
      (_, IsInstance)                -> return No
      (_, IsInstanceOnlyIf subgoals) -> (\(t:ts) -> foldl' truthOr t ts) <$> sequence [ isAffine t | (Instance (_ :< TyApply (_ :< TyCon "Copy") t)) <- subgoals ]
    Nothing                          -> return Yes


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


-- When we encounter a polymorphic function with constraints, we should add the constraints to the assumption set when type checking the body.
-- However, since the solver acts globally, the best we can do is add the constraints to the global assumption set.
-- We need to be extra careful about the constraints introduced (to avoid unsatisfiable constraints which cause bad global deductions),
-- in particular we require all of the constraints to only include the bound type variables at their leaves.
--
-- We also "expand" the assumptions, e.g. if there is an instance C t => D t, the the assumption D t should also include C t.

-- TODO handle views!
assumeFromQType :: [Annotated QTyVar] -> [Annotated TyConstraint] -> Praxis ()
assumeFromQType boundVars constraints = mapM_ assumeConstraint constraints where

  assumeConstraint :: Annotated TyConstraint -> Praxis ()
  assumeConstraint constraint = do
    constraint <- normalise constraint
    checkConstraint constraint
    constraints <- expandConstraint (view source constraint) (view value constraint)
    tyCheckState . assumptions %= Set.union (Set.fromList constraints)

  expandConstraint :: Source -> TyConstraint -> Praxis [TyConstraint]
  expandConstraint src constraint = ((constraint:) <$>) $ case constraint of
    Instance (a0 :< inst) -> case inst of
      TyApply (a1 :< TyCon cls) t -> case view value t of
        TyPair t1 t2 -> expandTyConInstance cls "Pair" [t1, t2]
        TyFn t1 t2 -> expandTyConInstance cls "Fn" [t1, t2]
        TyUnit -> expandTyConInstance cls "Unit" []
        TyVar _ -> return []
        _ | Just (n, ts) <- unapplyTyCon t -> expandTyConInstance cls n ts
    where
      expandTyConInstance :: Name -> Name -> [Annotated Type] -> Praxis [TyConstraint]
      expandTyConInstance cls name args = do
        l <- use iEnv
        let Just instances = Env.lookup name l
        case Map.lookup cls instances of
          Just resolver -> case resolver args of
            (_, IsInstance)          -> throwAt src ("redundant constraint: " <> pretty (phantom constraint))
            (_, IsInstanceOnlyIf cs) -> concat <$> mapM (expandConstraint src) cs
          _ -> return [] -- Note: The instance may be satisfied later (at the call site)

  boundVarNames = Set.fromList $ map (\boundVar -> case boundVar of { (_ :< QTyVar n) -> n; (_ :< QViewVar _ n) -> n }) boundVars

  checkConstraint :: Annotated TyConstraint -> Praxis ()
  checkConstraint constraint = case view value constraint of
    Instance (_ :< TyApply _ ty) -> checkConstraintType ty where
      checkConstraintType :: Annotated Type -> Praxis ()
      checkConstraintType (a@(src, _) :< ty) = case ty of
        TyPair t1 t2
          -> checkConstraintType t1 >> checkConstraintType t2
        TyFn t1 t2
          -> checkConstraintType t1 >> checkConstraintType t2
        TyVar n | n `elem` boundVarNames
          -> return ()
        _ | Just (n, ts@(_:_)) <- unapplyTyCon (a :< ty)
          -> mapM_ checkConstraintType ts
        _
          -> throwAt src $ "illegal constraint: " <> pretty constraint
