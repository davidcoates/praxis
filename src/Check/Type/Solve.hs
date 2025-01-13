{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeFamilies       #-}

module Check.Type.Solve
  ( assumeFromQType
  , run
  , normalize
  ) where

import           Check.Solve
import           Check.State
import           Common
import           Inbuilts            (copy)
import           Introspect
import           Praxis
import           Stage
import           Term

import           Control.Applicative (liftA2)
import           Data.List           (foldl', nub, partition, sort)
import qualified Data.Map.Strict     as Map
import           Data.Maybe          (fromMaybe)
import           Data.Set            (Set)
import qualified Data.Set            as Set


run :: IsTerm a => Annotated TypeCheck a -> Praxis (Annotated TypeCheck a)
run term = do
  -- TODO pretty ugly to do this here
  checkState . typeState . varEnv %%= traverse (second normalize)
  checkState . typeState . conEnv %%= traverse normalize
  checkState . typeState . typeSolve . requirements %%= (\set -> Set.fromList <$> traverse normalize (Set.toList set))
  checkState . typeState . typeSolve . assumptions %%= (\set -> Set.fromList <$> traverse normalize (Set.toList set))
  term <- normalize term
  term <- solve (checkState . typeState . typeSolve) reduce term
  term <- tryDefault term
  return term

unapplyTypeCon :: Annotated TypeCheck Type -> Maybe (Name, [Annotated TypeCheck Type])
unapplyTypeCon (_ :< ty) = case ty of
  TypeCon n -> Just (n, [])
  TypeApply ty1 ty2 -> case unapplyTypeCon ty1 of
    Just (n, tys) -> Just (n, tys ++ [ty2])
    Nothing       -> Nothing
  _ -> Nothing

assertNormalized :: (IsTerm a, Eq (a TypeCheck))  => Annotated TypeCheck a -> Praxis ()
assertNormalized term = do
  term' <- normalize term
  let str1 = fold (pretty term)
  let str2 = fold (pretty term')
  when (term /= term') $ throw TypeCheck ("unnormalized: " <> pretty term <> " vs " <> pretty term')
  return ()

reduce :: Disambiguating (Reducer TypeCheck)
reduce disambiguate (a :< constraint) = assertNormalized (a :< constraint) >> case constraint of

  TypeIsEq ty1 ty2 | ty1 == ty2 -> return tautology

  TypeIsEq (_ :< TypeUni Value x) ty
    | x `Set.member` typeUnis ty -> return contradiction
    | otherwise                  -> solvedWithSubgoals (x `is` view value ty) [ Subgoal (a :< TypeIsValue ty) ]

  TypeIsEq op1 op2@(_ :< TypeUni Value _) -> return $ subgoals [ Subgoal (a :< TypeIsEq op2 op1) ] -- handled by the above case

  TypeIsEq (_ :< TypeUni Plain x) ty
    | x `Set.member` typeUnis ty -> return contradiction
    | otherwise                  -> solved (x `is` view value ty)

  TypeIsEq op1 op2@(_ :< TypeUni Plain _) -> return $ subgoals [ Subgoal (a :< TypeIsEq op2 op1) ] -- handled by the above case

  TypeIsEq op1@(_ :< TypeUni View x) op2 -> do
    let op2' = op2 `removeTypeOp` op1
    solved (x `is` view value op2')

  TypeIsEq op1 op2@(_ :< TypeUni View _) -> return $ subgoals [ Subgoal (a :< TypeIsEq op2 op1) ] -- handled by the above case

  TypeIsEq op1@(_ :< TypeUni Ref x) op2 -> do
    let op2' = op2 `removeTypeOp` op1
    solvedWithSubgoals (x `is` (view value op2')) [ Subgoal (a :< TypeIsRef op1) ]

  TypeIsEq op1 op2@(_ :< TypeUni Ref _) -> return $ subgoals [ Subgoal (a :< TypeIsEq op2 op1) ] -- handled by the above case

  TypeIsEq ty1 ty2
    | (Just (n1, ty1s), Just (n2, ty2s)) <- (unapplyTypeCon ty1, unapplyTypeCon ty2) ->
      if n1 == n2
        then return $ subgoals (zipWith (\ty1 ty2 -> Subgoal (a :< TypeIsEq ty1 ty2)) ty1s ty2s)
        else return contradiction

  TypeIsEq (_ :< TypePair ty1 ty2) (_ :< TypePair ty3 ty4) -> return $ subgoals [ Subgoal (a :< TypeIsEq ty1 ty3), Subgoal (a :< TypeIsEq ty2 ty4) ]

  TypeIsEq (_ :< TypeFn ty1 ty2) (_ :< TypeFn ty3 ty4) -> return $ subgoals [ Subgoal (a :< TypeIsEq ty1 ty3), Subgoal (a :< TypeIsEq ty2 ty4) ]

  TypeIsEq ty1'@(_ :< TypeApplyOp _ _) ty2' -> do
    let
      (op1, ty1) = splitTypeOp ty1'
      (op2, ty2) = splitTypeOp ty2'
    let
      split = subgoals [ Subgoal (a :< TypeIsEq ty1 ty2), Subgoal (a :< TypeIsEqIfAffine op1 op2 ty1) ]
    if disambiguate
      then return split
      else case (view value ty1, view value ty2) of
        (TypeUni Plain _, _) -> return skip
        (_, TypeUni Plain _) -> return skip
        _                    -> return split

  TypeIsEq ty1 ty2@(_ :< TypeApplyOp _ _) -> reduce disambiguate (a :< TypeIsEq ty2 ty1) -- handled by the above case

  TypeIsEq op1@(_ :< TypeIdentityOp) op2 -> do
    case isRef op2 of
      Yes -> return contradiction
      Variable -> return contradiction
      _ -> do
        let viewUnis = [ (x, TypeIdentityOp) | (_ :< TypeUni View x) <- Set.toList (expandTypeOps op2) ]
        solved (are viewUnis)

  TypeIsEq op1 op2@(_ :< TypeIdentityOp) -> return $ subgoals [ Subgoal (a :< TypeIsEq op2 op1) ] -- handled by the above case

  TypeIsEqIfAffine op1 op2 ty -> do
    affine <- isAffine ty
    case affine of
      No      -> return tautology
      Unknown -> return skip
      _       -> return $ subgoals [ Subgoal (a :< TypeIsEq op1 op2) ]

  TypeIsSub ty1' ty2'@(_ :< TypeApplyOp _ _) -> do
    let
      (op1, ty1) = splitTypeOp ty1'
      (op2, ty2) = splitTypeOp ty2'
    case (view value ty1, view value ty2) of
      (TypeUni Plain _, _) -> return skip
      (_, TypeUni Plain _) -> return skip
      _                    -> return $ subgoals [ Subgoal (a :< TypeIsEq ty1 ty2), Subgoal (a :< TypeIsSubIfAffine op1 op2 ty1) ]

  TypeIsSub _ (_ :< TypeUni Plain _) -> return skip

  TypeIsSub op1 op2 | isTypeOp op1 -> do
    if expandTypeOps op1 `Set.isSubsetOf` expandTypeOps op2
      then return tautology
      else return skip

  TypeIsSub ty1 ty2 -> return $ subgoals [ Subgoal (a :< TypeIsEq ty1 ty2) ]

  TypeIsSubIfAffine op1 op2 ty -> do
    affine <- isAffine ty
    case affine of
      No      -> return tautology
      Unknown -> return skip
      _       -> return $ subgoals [ Subgoal (a :< TypeIsSub op1 op2) ]

  TypeIsRef op -> do
    case isRef op of
      Yes     -> return tautology
      Unknown -> return skip
      _       -> return contradiction

  TypeIsValue (_ :< ty) -> case ty of
    TypeApplyOp op ty -> do
      affine <- isAffine ty
      case affine of
        Unknown  -> return skip
        No       -> error "unnormalized"
        _        -> return $ subgoals [ Subgoal (a :< TypeIsEq op (phantom TypeIdentityOp)), Subgoal (a :< TypeIsValue ty) ]
    TypeVar Plain _ -> return contradiction
    TypeUni Plain _ -> return skip
    _               -> return tautology

  TypeIsRefFree ty refLabel
    | Set.null (typeUnis ty)
      -> if refLabel `Set.member` refLabels ty then return contradiction else return tautology
    | otherwise
      -> return skip

  TypeIsInstance (a0 :< inst) -> case inst of

    TypeApply (_ :< TypeCon "Integral") ty | disambiguate
      -> return $ subgoals [ Subgoal (a :< TypeIsEq ty (phantom (TypeCon "I32"))) ]

    TypeApply (a1 :< TypeCon cls) ty -> case view value ty of
      TypeApplyOp op ty -> do
        let
          instVal = phantom (TypeIsInstance (a0 :< TypeApply (a1 :< TypeCon cls) ty))
          instRef = phantom (TypeIsInstance (a0 :< TypeApply (a1 :< TypeCon cls) (phantom (TypeApply (phantom (TypeCon "Ref")) ty))))
        affine <- isAffine ty
        case (isRef op, affine) of
          (No, _)         -> error "unnormalized"
          (_, No)         -> error "unnormalized"
          (_, Unknown)    -> return skip
          (Unknown, _)    -> return skip
          (Yes, Yes)      -> reduceTypeConInstance cls "Ref" [ty]
          (Yes, Variable) -> return $ subgoals [ Subgoal instRef, copy ty `Implies` instVal ]
          (Variable, _)   -> return $ subgoals [ Subgoal instRef, Subgoal instVal ]
      TypePair ty1 ty2 -> reduceTypeConInstance cls "Pair" [ty1, ty2]
      TypeFn ty1 ty2 -> reduceTypeConInstance cls "Fn" [ty1, ty2]
      TypeUnit -> reduceTypeConInstance cls "Unit" []
      TypeVar _ _ -> return contradiction
      _ | Just (n, tys) <- unapplyTypeCon ty -> reduceTypeConInstance cls n tys
      _ -> return skip

  TypeIsIntegralOver (_ :< ty) n -> case ty of
    TypeCon "I8"    -> checkBounds n (undefined :: I8)
    TypeCon "I16"   -> checkBounds n (undefined :: I16)
    TypeCon "I32"   -> checkBounds n (undefined :: I32)
    TypeCon "I64"   -> checkBounds n (undefined :: I64)
    TypeCon "ISize" -> checkBounds n (undefined :: ISize)
    TypeCon "U8"    -> checkBounds n (undefined :: U8)
    TypeCon "U16"   -> checkBounds n (undefined :: U16)
    TypeCon "U32"   -> checkBounds n (undefined :: U32)
    TypeCon "U64"   -> checkBounds n (undefined :: U64)
    TypeCon "USize" -> checkBounds n (undefined :: USize)
    _               -> return skip
    where
      checkBounds :: forall a. (Integral a, Bounded a) => Integer -> a -> Praxis (Reduction TypeCheck)
      checkBounds n _ = if toInteger (minBound :: a) <= n && n <= toInteger (maxBound :: a) then return tautology else return contradiction

  _ -> return contradiction


  where
    reduceTypeConInstance :: Name -> Name -> [Annotated TypeCheck Type] -> Praxis (Reduction TypeCheck)
    reduceTypeConInstance cls name args = do
      l <- use (checkState . instanceEnv)
      let Just instances = Map.lookup name l
      case Map.lookup cls instances of
        Just resolver -> case resolver args of
          (_, IsInstance)          -> return tautology
          (_, IsInstanceOnlyIf cs) -> do
            cs <- traverse normalize cs
            return (subgoals (map Subgoal cs))
        Nothing -> return contradiction

    typeUnis :: forall a. IsTerm a => Annotated TypeCheck a -> Set Name
    typeUnis = extract (embedMonoid f) where
      f (_ :< ty) = case ty of
        TypeUni _ n -> Set.singleton n
        _           -> Set.empty

    refLabels :: forall a. IsTerm a => Annotated TypeCheck a -> Set Name
    refLabels = extract (embedMonoid f) where
      f (_ :< ty) = case ty of
        TypeRef n -> Set.singleton n
        _         -> Set.empty


-- Rewrite helpers
solved :: Resolver TypeCheck -> Praxis (Reduction TypeCheck)
solved resolve = solvedWithSubgoals resolve []

-- note: assumption is the subgoals are not affected by the solution
solvedWithSubgoals :: Resolver TypeCheck -> [Subgoal TypeCheck] -> Praxis (Reduction TypeCheck)
solvedWithSubgoals resolve subgoals = do
  checkState . typeState . varEnv %%= traverse (second (normalize . sub resolve))
  checkState . typeState . conEnv %%= traverse (normalize . sub resolve)
  return (Progress (Just (resolve, normalize)) subgoals)

are :: [(Name, Type TypeCheck)] -> Resolver TypeCheck
are ops = embedSub f where
  f (a :< x) = case x of
    TypeUni _ n -> case n `lookup` ops of { Just op -> Just (a :< op); Nothing -> Nothing }
    _           -> Nothing

is :: Name -> Type TypeCheck -> Resolver TypeCheck
is n ty = embedSub f where
  f (a :< x) = case x of
    TypeUni _ n' -> if n == n' then Just (a :< ty) else Nothing
    _            -> Nothing

-- TypeOp helpers
splitTypeOp :: Annotated TypeCheck Type -> (Annotated TypeCheck Type, Annotated TypeCheck Type)
splitTypeOp ty = case view value ty of
  TypeApplyOp op ty -> (op, ty)
  _                 -> (phantom TypeIdentityOp, ty)

expandTypeOps :: Annotated TypeCheck Type -> Set (Annotated TypeCheck Type)
expandTypeOps op = case view value op of
  TypeIdentityOp -> Set.empty
  TypeSetOp ops  -> ops
  _              -> Set.singleton op

contractTypeOps :: Set (Annotated TypeCheck Type) -> Annotated TypeCheck Type
contractTypeOps ops = case Set.toList ops of
  []   -> phantom TypeIdentityOp
  [op] -> op
  _    -> phantom (TypeSetOp ops) -- TODO source is lost

removeTypeOp :: Annotated TypeCheck Type -> Annotated TypeCheck Type -> Annotated TypeCheck Type
removeTypeOp op1 op2  = contractTypeOps (expandTypeOps op1 `Set.difference` expandTypeOps op2)

-- Term normalizer (after a substitution is applied)
normalize :: Normalizer TypeCheck
normalize (a :< x) = case typeof x of

  TypeT -> case x of

    TypeApplyOp op ty -> do
      op <- normalize op
      ty <- normalize ty
      case op of
        (_ :< TypeIdentityOp) -> return ty
        _ -> case ty of
          (_ :< TypeApplyOp op' ty') -> return $ (a :< TypeApplyOp (contractTypeOps (Set.fromList [op, op'])) ty')
          _ -> do
            affine <- isAffine ty
            case affine of
              No -> return ty
              _  -> return (a :< TypeApplyOp op ty)

    TypeSetOp ops -> do
      ops <- traverse normalize (Set.toList ops)
      return $ (contractTypeOps . Set.unions . map expandTypeOps) ops

    _ -> continue

  _ -> continue

  where
    continue = recurse normalize (a :< x)


data Truth = Yes | No | Variable | Unknown
  deriving Show

isRef :: Annotated TypeCheck Type -> Truth
isRef op = case view value op of
  TypeIdentityOp -> No
  TypeRef _      -> Yes
  TypeSetOp ops  -> foldr (\op -> truthOr (isRef op)) No ops
  TypeUni Ref _  -> Yes
  TypeUni View _ -> Unknown
  TypeVar Ref _  -> Yes
  TypeVar View _ -> Variable

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

isAffine :: Annotated TypeCheck Type -> Praxis Truth
isAffine ty = do
  assumptions' <- use (checkState . typeState . typeSolve . assumptions)
  if copy ty `Set.member` assumptions'
    then return No
    else isAffine' ty
  where
    isAffine' :: Annotated TypeCheck Type -> Praxis Truth
    isAffine' (a :< ty) = case ty of
      TypePair ty1 ty2 -> isTypeConAffine "Pair" [ty1, ty2]
      TypeFn ty1 ty2 -> isTypeConAffine "Fn" [ty1, ty2]
      TypeUnit -> isTypeConAffine "Unit" []
      TypeApplyOp op ty -> truthAnd (truthNot (isRef op)) <$> isAffine ty
      TypeUni _ _ -> return Unknown
      TypeVar _ _ -> return Variable
      _ | Just (n, tys) <- unapplyTypeCon (a :< ty) -> isTypeConAffine n tys

isTypeConAffine :: Name -> [Annotated TypeCheck Type] -> Praxis Truth
isTypeConAffine name args = do
  l <- use (checkState . instanceEnv)
  let Just instances = Map.lookup name l
  case Map.lookup "Copy" instances of
    Just resolver -> case resolver args of
      (_, IsInstance)                -> return No
      (_, IsInstanceOnlyIf subgoals) -> (\(t:ts) -> foldl' truthOr t ts) <$> sequence [ isAffine ty | (_ :< TypeIsInstance (_ :< TypeApply (_ :< TypeCon "Copy") ty)) <- subgoals ]
    Nothing                          -> return Yes


-- Check for undetermined unification variables, default them where possible
tryDefault :: IsTerm a => Annotated TypeCheck a -> Praxis (Annotated TypeCheck a)
tryDefault term@((src, _) :< _) = do

  -- TODO could just be a warning, and default to ()?
  let freeTys = deepTypeUnis (\f -> f == Plain || f == Value) term
  when (not (null freeTys)) $ throwAt TypeCheck src $ "underdetermined type " <> pretty (Set.elemAt 0 freeTys)

  let
    defaultRef name = do
      ref <- freshRef
      warnAt TypeCheck src $ "underdetermined reference " <> pretty name <> ", defaulting to " <> pretty ref
      return (name, view value ref)

    defaultView name = do
      warnAt TypeCheck src $ "underdetermined view " <> pretty name <> ", defaulting to " <> pretty (phantom TypeIdentityOp :: Annotated TypeCheck Type)
      return (name, TypeIdentityOp)

  defaultViews <- traverse defaultView (Set.toList (deepTypeUnis (== View) term))
  defaultRefs <- traverse defaultRef (Set.toList (deepTypeUnis (== Ref) term))

  let defaultTypeOps = defaultViews ++ defaultRefs

  case defaultTypeOps of
    [] -> return term
    _  -> do
      Progress (Just (resolve, normalize)) _ <- solved (are defaultTypeOps)
      (normalize . sub resolve) term

  where
    deepTypeUnis :: forall a. IsTerm a => (Flavor -> Bool) -> Annotated TypeCheck a -> Set Name
    deepTypeUnis matchFlavor = deepExtract (embedMonoid f) where
      f (_ :< ty) = case ty of
        TypeUni f n -> if matchFlavor f then Set.singleton n else Set.empty
        _           -> Set.empty


-- When we encounter a polymorphic function with constraints, we should add the constraints to the assumption set when type checking the body.
-- However, since the solver acts globally, the best we can do is add the constraints to the global assumption set.
-- We need to be extra careful about the constraints introduced (to avoid unsatisfiable constraints which cause bad global deductions),
-- in particular we require all of the constraints to only include the bound type variables at their leaves.
--
-- We also "expand" the assumptions, e.g. if there is an instance C t => D t, the the assumption D t should also include C t.

-- TODO handle references/views!
assumeFromQType :: [Annotated TypeCheck TypePat] -> [Annotated TypeCheck TypeConstraint] -> Praxis ()
assumeFromQType boundVars constraints = mapM_ assumeConstraint constraints where

  assumeConstraint :: Annotated TypeCheck TypeConstraint -> Praxis ()
  assumeConstraint constraint = do
    constraint <- normalize constraint
    checkConstraint constraint
    constraints <- expandConstraint constraint
    checkState . typeState . typeSolve . assumptions %= Set.union (Set.fromList constraints)

  expandConstraint :: Annotated TypeCheck TypeConstraint -> Praxis [Annotated TypeCheck TypeConstraint]
  expandConstraint constraint@((src, _) :< _) = ((constraint:) <$>) $ case view value constraint of
    TypeIsInstance (a0 :< inst) -> case inst of
      TypeApply (a1 :< TypeCon cls) ty -> case view value ty of
        TypePair ty1 ty2 -> expandTypeConInstance cls "Pair" [ty1, ty2]
        TypeFn ty1 ty2 -> expandTypeConInstance cls "Fn" [ty1, ty2]
        TypeUnit -> expandTypeConInstance cls "Unit" []
        TypeVar _ _ -> return []
        _ | Just (n, tys) <- unapplyTypeCon ty -> expandTypeConInstance cls n tys
    where
      expandTypeConInstance :: Name -> Name -> [Annotated TypeCheck Type] -> Praxis [Annotated TypeCheck TypeConstraint]
      expandTypeConInstance cls name args = do
        l <- use (checkState . instanceEnv)
        let Just instances = Map.lookup name l
        case Map.lookup cls instances of
          Just resolver -> case resolver args of
            (_, IsInstance)          -> throwAt TypeCheck src ("redundant constraint: " <> pretty constraint)
            (_, IsInstanceOnlyIf cs) -> concat <$> traverse expandConstraint cs
          _ -> return [] -- Note: The instance may be satisfied later (at the call site)

  checkConstraint :: Annotated TypeCheck TypeConstraint -> Praxis ()
  checkConstraint constraint = case view value constraint of
    TypeIsInstance (_ :< TypeApply _ ty) -> checkConstraintType ty where
      checkConstraintType :: Annotated TypeCheck Type -> Praxis ()
      checkConstraintType (a@(src, _) :< ty) = case ty of
        TypePair ty1 ty2
          -> checkConstraintType ty1 >> checkConstraintType ty2
        TypeFn ty1 ty2
          -> checkConstraintType ty1 >> checkConstraintType ty2
        TypeVar _ n | n `elem` Set.fromList (map (\(_ :< TypePatVar _ n) -> n) boundVars)
          -> return ()
        _ | Just (n, tys@(_:_)) <- unapplyTypeCon (a :< ty)
          -> traverse checkConstraintType tys >> return ()
        _
          -> throwAt TypeCheck src $ "illegal constraint: " <> pretty constraint
        -- TODO RefVar and ViewVar ?
