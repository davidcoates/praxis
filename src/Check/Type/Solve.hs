{-# LANGUAGE ImpredicativeTypes   #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Check.Type.Solve
  ( assumeFromQType
  , run
  , normalize
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
import           Data.List           (foldl', nub, partition, sort)
import qualified Data.Map.Strict     as Map
import           Data.Maybe          (fromMaybe)
import           Data.Set            (Set)
import qualified Data.Set            as Set


run :: Term a => Annotated a -> Praxis (Annotated a)
run term = do
  -- TODO pretty ugly to do this here
  checkState . typeState . tEnv %%= traverse (LEnv.value normalize)
  checkState . typeState . typeSolve . requirements %%= (\set -> Set.fromList <$> traverse normalize (Set.toList set))
  checkState . typeState . typeSolve . assumptions %%= (\set -> Set.fromList <$> traverse (\c -> view value <$> normalize (phantom c)) (Set.toList set))
  term <- normalize term
  term <- solve (checkState . typeState . typeSolve) reduce term
  term <- tryDefault term
  return term

unapplyTypeCon :: Annotated Type -> Maybe (Name, [Annotated Type])
unapplyTypeCon (_ :< ty) = case ty of
  TypeCon n -> Just (n, [])
  TypeApply t1 t2 -> case unapplyTypeCon t1 of
    Just (n, ts) -> Just (n, ts ++ [t2])
    Nothing      -> Nothing
  _ -> Nothing

assertNormalised :: (Eq a, Term a) => Annotated a -> Praxis ()
assertNormalised term = do
  term' <- normalize term
  let str1 = fold (runPrintable (pretty term) Simple)
  let str2 = fold (runPrintable (pretty term') Simple)
  when (term /= term') $ throw ("unnormalized: " <> pretty term <> " vs " <> pretty term')
  return ()

reduce :: Disambiguating (Reducer TypeConstraint)
reduce disambiguate constraint = assertNormalised (phantom constraint) >> case constraint of

  TypeIsEq t1 t2 | t1 == t2 -> return tautology

  TypeIsEq (_ :< TypeUni Value x) t
    | x `Set.member` typeUnis t -> return contradiction
    | otherwise               -> solvedWithSubgoals (x `is` view value t) [ Subgoal (TypeIsValue t) ]

  TypeIsEq op1 op2@(_ :< TypeUni Value _) -> return $ subgoals [ Subgoal (TypeIsEq op2 op1) ] -- handled by the above case

  TypeIsEq (_ :< TypeUni Plain x) t
    | x `Set.member` typeUnis t -> return contradiction
    | otherwise               -> solved (x `is` view value t)

  TypeIsEq op1 op2@(_ :< TypeUni Plain _) -> return $ subgoals [ Subgoal (TypeIsEq op2 op1) ] -- handled by the above case

  TypeIsEq op1@(_ :< TypeUni View x) op2 -> do
    let op2' = op2 `removeTypeOp` op1
    solved (x `is` view value op2')

  TypeIsEq op1 op2@(_ :< TypeUni View _) -> return $ subgoals [ Subgoal (TypeIsEq op2 op1) ] -- handled by the above case

  TypeIsEq op1@(_ :< TypeUni Ref x) op2 -> do
    let op2' = op2 `removeTypeOp` op1
    solvedWithSubgoals (x `is` (view value op2')) [ Subgoal (TypeIsRef op1) ]

  TypeIsEq op1 op2@(_ :< TypeUni Ref _) -> return $ subgoals [ Subgoal (TypeIsEq op2 op1) ] -- handled by the above case

  TypeIsEq t1 t2
    | (Just (n1, t1s), Just (n2, t2s)) <- (unapplyTypeCon t1, unapplyTypeCon t2) ->
      if n1 == n2
        then return $ subgoals (zipWith (\t1 t2 -> Subgoal (TypeIsEq t1 t2)) t1s t2s)
        else return contradiction

  TypeIsEq (_ :< TypePair s1 s2) (_ :< TypePair t1 t2) -> return $ subgoals [ Subgoal (TypeIsEq s1 t1), Subgoal (TypeIsEq s2 t2) ]

  TypeIsEq (_ :< TypeFn t1 t2) (_ :< TypeFn s1 s2) -> return $ subgoals [ Subgoal (TypeIsEq t1 s1), Subgoal (TypeIsEq t2 s2) ]

  TypeIsEq t1'@(_ :< TypeApplyOp _ _) t2' -> do
    let
      (op1, t1) = splitTypeOp t1'
      (op2, t2) = splitTypeOp t2'
    let
      split = subgoals [ Subgoal (TypeIsEq t1 t2), Subgoal (TypeIsEqIfAffine op1 op2 t1) ]
    if disambiguate
      then return split
      else case (view value t1, view value t2) of
        (TypeUni Plain _, _) -> return skip
        (_, TypeUni Plain _) -> return skip
        _                    -> return split

  TypeIsEq t1 t2@(_ :< TypeApplyOp _ _) -> reduce disambiguate (TypeIsEq t2 t1) -- handled by the above case

  TypeIsEq op1@(_ :< TypeIdentityOp) op2 -> do
    case isRef op2 of
      Yes -> return contradiction
      Variable -> return contradiction
      _ -> do
        let viewUnis = [ (x, TypeIdentityOp) | (_ :< TypeUni View x) <- Set.toList (expandTypeOps op2) ]
        solved (are viewUnis)

  TypeIsEq op1 op2@(_ :< TypeIdentityOp) -> return $ subgoals [ Subgoal (TypeIsEq op2 op1) ] -- handled by the above case

  TypeIsEqIfAffine op1 op2 t -> do
    affine <- isAffine t
    case affine of
      No      -> return tautology
      Unknown -> return skip
      _       -> return $ subgoals [ Subgoal (TypeIsEq op1 op2) ]

  TypeIsSub t1' t2'@(_ :< TypeApplyOp _ _) -> do
    let
      (op1, t1) = splitTypeOp t1'
      (op2, t2) = splitTypeOp t2'
    case (view value t1, view value t2) of
      (TypeUni Plain _, _) -> return skip
      (_, TypeUni Plain _) -> return skip
      _                    -> return $ subgoals [ Subgoal (TypeIsEq t1 t2), Subgoal (TypeIsSubIfAffine op1 op2 t1) ]

  TypeIsSub _ (_ :< TypeUni Plain _) -> return skip

  TypeIsSub op1 op2 | isTypeOp op1 -> do
    if expandTypeOps op1 `Set.isSubsetOf` expandTypeOps op2
      then return tautology
      else return skip

  TypeIsSub t1 t2 -> return $ subgoals [ Subgoal (TypeIsEq t1 t2) ]

  TypeIsSubIfAffine op1 op2 t -> do
    affine <- isAffine t
    case affine of
      No      -> return tautology
      Unknown -> return skip
      _       -> return $ subgoals [ Subgoal (TypeIsSub op1 op2) ]

  TypeIsRef op -> do
    case isRef op of
      Yes     -> return tautology
      Unknown -> return skip
      _       -> return contradiction

  TypeIsValue (_ :< t) -> case t of
    TypeApplyOp op t -> do
      affine <- isAffine t
      case affine of
        Unknown  -> return skip
        No       -> error "unnormalized"
        _        -> return $ subgoals [ Subgoal (TypeIsEq op (TypeIdentityOp `as` phantom KindView)), Subgoal (TypeIsValue t) ]
    TypeVar Plain _ -> return contradiction
    TypeUni Plain _ -> return skip
    _               -> return tautology

  TypeIsRefFree t refLabel
    | Set.null (typeUnis t)
      -> if refLabel `Set.member` refLabels t then return contradiction else return tautology
    | otherwise
      -> return skip

  TypeIsInstance (a0 :< inst) -> case inst of

    TypeApply (_ :< TypeCon "Integral") t | disambiguate
      -> return $ subgoals [ Subgoal (TypeIsEq t (TypeCon "I32" `as` phantom KindType)) ]

    TypeApply (a1 :< TypeCon cls) t -> case view value t of
      TypeApplyOp op t -> do
        let
          instVal = TypeIsInstance (a0 :< TypeApply (a1 :< TypeCon cls) t)
          instRef = TypeIsInstance (a0 :< TypeApply (a1 :< TypeCon cls) (phantom (TypeApply (phantom (TypeCon "Ref")) t)))
        affine <- isAffine t
        case (isRef op, affine) of
          (No, _)         -> error "unnormalized"
          (_, No)         -> error "unnormalized"
          (_, Unknown)    -> return skip
          (Unknown, _)    -> return skip
          (Yes, Yes)      -> reduceTypeConInstance cls "Ref" [t]
          (Yes, Variable) -> return $ subgoals [ Subgoal instRef, copy t `Implies` instVal ]
          (Variable, _)   -> return $ subgoals [ Subgoal instRef, Subgoal instVal ]
      TypePair t1 t2 -> reduceTypeConInstance cls "Pair" [t1, t2]
      TypeFn t1 t2 -> reduceTypeConInstance cls "Fn" [t1, t2]
      TypeUnit -> reduceTypeConInstance cls "Unit" []
      TypeVar _ _ -> return contradiction
      _ | Just (n, ts) <- unapplyTypeCon t -> reduceTypeConInstance cls n ts
      _ -> return skip

  TypeIsIntegralOver (_ :< t) n -> case t of
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
      checkBounds :: forall a. (Integral a, Bounded a) => Integer -> a -> Praxis (Reduction TypeConstraint)
      checkBounds n _ = if toInteger (minBound :: a) <= n && n <= toInteger (maxBound :: a) then return tautology else return contradiction

  _ -> return contradiction


  where
    reduceTypeConInstance :: Name -> Name -> [Annotated Type] -> Praxis (Reduction TypeConstraint)
    reduceTypeConInstance cls name args = do
      l <- use (checkState . iEnv)
      let Just instances = Env.lookup name l
      case Map.lookup cls instances of
        Just resolver -> case resolver args of
          (_, IsInstance)          -> return tautology
          (_, IsInstanceOnlyIf cs) -> do
            cs <- mapM (\c -> view value <$> normalize (phantom c)) cs
            return (subgoals (map Subgoal cs))
        Nothing -> return contradiction

    typeUnis :: forall a. Term a => Annotated a -> Set Name
    typeUnis = extract (embedMonoid f) where
      f x = case x of
        TypeUni _ n -> Set.singleton n
        _           -> Set.empty

    refLabels :: forall a. Term a => Annotated a -> Set Name
    refLabels = extract (embedMonoid f) where
      f = \case
        TypeRef n -> Set.singleton n
        _         -> Set.empty


isTypeOp :: Annotated Type -> Bool
isTypeOp ty = case view (annotation . just . value) ty of
  KindView -> True
  KindRef  -> True
  _        -> False

-- Rewrite helpers
solved :: Resolver -> Praxis (Reduction TypeConstraint)
solved resolve = solvedWithSubgoals resolve []

-- note: assumption is the subgoals are not affected by the solution
solvedWithSubgoals :: Resolver -> [Subgoal TypeConstraint] -> Praxis (Reduction TypeConstraint)
solvedWithSubgoals resolve subgoals = do
  checkState . typeState . tEnv %%= traverse (LEnv.value (normalize . sub resolve))
  return (Progress (Just (resolve, normalize)) subgoals)

are :: [(Name, Type)] -> Resolver
are ops = embedSub f where
  f (a :< x) = case x of
    TypeUni _ n -> case n `lookup` ops of { Just op -> Just (a :< op); Nothing -> Nothing }
    _           -> Nothing

is :: Name -> Type -> Resolver
is n t = embedSub f where
  f (a :< x) = case x of
    TypeUni _ n' -> if n == n' then Just (a :< t) else Nothing
    _            -> Nothing

-- TypeOp helpers
splitTypeOp :: Annotated Type -> (Annotated Type, Annotated Type)
splitTypeOp ty = case view value ty of
  TypeApplyOp op ty -> (op, ty)
  _                 -> (TypeIdentityOp `as` phantom KindView, ty)

expandTypeOps :: Annotated Type -> Set (Annotated Type)
expandTypeOps op = case view value op of
  TypeIdentityOp -> Set.empty
  TypeSetOp ops  -> ops
  _              -> Set.singleton op

contractTypeOps :: Set (Annotated Type) -> Annotated Type
contractTypeOps ops = case Set.toList ops of
  []   -> TypeIdentityOp `as` phantom KindView
  [op] -> op
  _    -> (Phantom, Just kind) :< TypeSetOp ops where -- TODO source is lost
    kind :: Annotated Kind
    kind = let (k:ks) = map (view (annotation . just)) (Set.toList ops) in foldr combineKinds k ks
    combineKinds :: Annotated Kind -> Annotated Kind -> Annotated Kind
    combineKinds (_ :< k1) (_ :< k2) = ((Phantom, Nothing) :<) $ case (k1, k2) of
      (KindView, KindView) -> KindView
      (KindRef, KindRef)   -> KindRef
      (KindView, KindRef)  -> KindRef
      (KindRef, KindView)  -> KindRef

removeTypeOp :: Annotated Type -> Annotated Type -> Annotated Type
removeTypeOp op1 op2  = contractTypeOps (expandTypeOps op1 `Set.difference` expandTypeOps op2)

-- Term normalizer (after a substitution is applied)
normalize :: Normaliser
normalize (a :< x) = case typeof x of

  IType -> case x of

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
      ops <- mapM normalize (Set.toList ops)
      return $ (contractTypeOps . Set.unions . map expandTypeOps) ops

    _ -> continue

  _ -> continue

  where
    continue = recurse normalize (a :< x)


data Truth = Yes | No | Variable | Unknown
  deriving Show

isRef :: Annotated Type -> Truth
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

isAffine :: Annotated Type -> Praxis Truth
isAffine t = do
  assumptions' <- use (checkState . typeState . typeSolve . assumptions)
  if copy t `Set.member` assumptions'
    then return No
    else isAffine' t
  where
    isAffine' :: Annotated Type -> Praxis Truth
    isAffine' (a :< t) = case t of
      TypePair t1 t2 -> isTypeConAffine "Pair" [t1, t2]
      TypeFn t1 t2 -> isTypeConAffine "Fn" [t1, t2]
      TypeUnit -> isTypeConAffine "Unit" []
      TypeApplyOp op t -> truthAnd (truthNot (isRef op)) <$> isAffine t
      TypeUni _ _ -> return Unknown
      TypeVar _ _ -> return Variable
      _ | Just (n, ts) <- unapplyTypeCon (a :< t) -> isTypeConAffine n ts

isTypeConAffine :: Name -> [Annotated Type] -> Praxis Truth
isTypeConAffine name args = do
  l <- use (checkState . iEnv)
  let Just instances = Env.lookup name l
  case Map.lookup "Copy" instances of
    Just resolver -> case resolver args of
      (_, IsInstance)                -> return No
      (_, IsInstanceOnlyIf subgoals) -> (\(t:ts) -> foldl' truthOr t ts) <$> sequence [ isAffine t | (TypeIsInstance (_ :< TypeApply (_ :< TypeCon "Copy") t)) <- subgoals ]
    Nothing                          -> return Yes


-- Check for undetermined unification variables, default them where possible
tryDefault :: Term a => Annotated a -> Praxis (Annotated a)
tryDefault term@((src, _) :< _) = do

  -- TODO could just be a warning, and default to ()?
  let freeTys = deepTypeUnis (\f -> f == Plain || f == Value) term
  when (not (null freeTys)) $ throwAt src $ "underdetermined type " <> pretty (Set.elemAt 0 freeTys)

  let
    defaultRef name = do
      ref <- freshRef
      warnAt src $ "underdetermined reference " <> pretty name <> ", defaulting to " <> pretty ref
      return (name, view value ref)

    defaultView name = do
      warnAt src $ "underdetermined view " <> pretty name <> ", defaulting to " <> pretty (phantom TypeIdentityOp)
      return (name, TypeIdentityOp)

  defaultViews <- mapM defaultView (Set.toList (deepTypeUnis (== View) term))
  defaultRefs <- mapM defaultRef (Set.toList (deepTypeUnis (== Ref) term))

  let defaultTypeOps = defaultViews ++ defaultRefs

  case defaultTypeOps of
    [] -> return term
    _  -> do
      Progress (Just (resolve, normalize)) _ <- solved (are defaultTypeOps)
      (normalize . sub resolve) term

  where
    deepTypeUnis :: forall a. Term a => (Flavor -> Bool) -> Annotated a -> Set Name
    deepTypeUnis matchFlavor = deepExtract (embedMonoid f) where
      f = \case
        TypeUni f n -> if matchFlavor f then Set.singleton n else Set.empty
        _           -> Set.empty


-- When we encounter a polymorphic function with constraints, we should add the constraints to the assumption set when type checking the body.
-- However, since the solver acts globally, the best we can do is add the constraints to the global assumption set.
-- We need to be extra careful about the constraints introduced (to avoid unsatisfiable constraints which cause bad global deductions),
-- in particular we require all of the constraints to only include the bound type variables at their leaves.
--
-- We also "expand" the assumptions, e.g. if there is an instance C t => D t, the the assumption D t should also include C t.

-- TODO handle references/views!
assumeFromQType :: [Annotated TypePat] -> [Annotated TypeConstraint] -> Praxis ()
assumeFromQType boundVars constraints = mapM_ assumeConstraint constraints where

  assumeConstraint :: Annotated TypeConstraint -> Praxis ()
  assumeConstraint constraint = do
    constraint <- normalize constraint
    checkConstraint constraint
    constraints <- expandConstraint (view source constraint) (view value constraint)
    checkState . typeState . typeSolve . assumptions %= Set.union (Set.fromList constraints)

  expandConstraint :: Source -> TypeConstraint -> Praxis [TypeConstraint]
  expandConstraint src constraint = ((constraint:) <$>) $ case constraint of
    TypeIsInstance (a0 :< inst) -> case inst of
      TypeApply (a1 :< TypeCon cls) t -> case view value t of
        TypePair t1 t2 -> expandTypeConInstance cls "Pair" [t1, t2]
        TypeFn t1 t2 -> expandTypeConInstance cls "Fn" [t1, t2]
        TypeUnit -> expandTypeConInstance cls "Unit" []
        TypeVar _ _ -> return []
        _ | Just (n, ts) <- unapplyTypeCon t -> expandTypeConInstance cls n ts
    where
      expandTypeConInstance :: Name -> Name -> [Annotated Type] -> Praxis [TypeConstraint]
      expandTypeConInstance cls name args = do
        l <- use (checkState . iEnv)
        let Just instances = Env.lookup name l
        case Map.lookup cls instances of
          Just resolver -> case resolver args of
            (_, IsInstance)          -> throwAt src ("redundant constraint: " <> pretty (phantom constraint))
            (_, IsInstanceOnlyIf cs) -> concat <$> mapM (expandConstraint src) cs
          _ -> return [] -- Note: The instance may be satisfied later (at the call site)

  checkConstraint :: Annotated TypeConstraint -> Praxis ()
  checkConstraint constraint = case view value constraint of
    TypeIsInstance (_ :< TypeApply _ ty) -> checkConstraintType ty where
      checkConstraintType :: Annotated Type -> Praxis ()
      checkConstraintType (a@(src, _) :< ty) = case ty of
        TypePair t1 t2
          -> checkConstraintType t1 >> checkConstraintType t2
        TypeFn t1 t2
          -> checkConstraintType t1 >> checkConstraintType t2
        TypeVar _ n | n `elem` Set.fromList (map (\(_ :< TypePatVar _ n) -> n) boundVars)
          -> return ()
        _ | Just (n, ts@(_:_)) <- unapplyTypeCon (a :< ty)
          -> mapM_ checkConstraintType ts
        _
          -> throwAt src $ "illegal constraint: " <> pretty constraint
        -- TODO RefVar and ViewVar ?
