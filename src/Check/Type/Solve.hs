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
  tEnv %%= traverse (LEnv.value normalize)
  tyCheckState . requirements %%= (\set -> Set.fromList <$> traverse normalize (Set.toList set))
  tyCheckState . assumptions %%= (\set -> Set.fromList <$> traverse (\c -> view value <$> normalize (phantom c)) (Set.toList set))
  term <- normalize term
  term <- solve tyCheckState reduce term
  term <- tryDefault term
  return term

unapplyTyCon :: Annotated Type -> Maybe (Name, [Annotated Type])
unapplyTyCon (_ :< ty) = case ty of
  TyCon n -> Just (n, [])
  TyApply t1 t2 -> case unapplyTyCon t1 of
    Just (n, ts) -> Just (n, ts ++ [t2])
    Nothing      -> Nothing
  _ -> Nothing

assertNormalised :: (Eq a, Term a) => Annotated a -> Praxis ()
assertNormalised term = do
  term' <- normalize term
  let str1 = fold (runPrintable (pretty term) Plain)
  let str2 = fold (runPrintable (pretty term') Plain)
  when (term /= term') $ throw ("unnormalized: " <> pretty term <> " vs " <> pretty term')
  return ()

reduce :: Disambiguating (Reducer TyConstraint)
reduce disambiguate constraint = assertNormalised (phantom constraint) >> case constraint of

  TEq t1 t2 | t1 == t2 -> return tautology

  TEq (_ :< TyUniValue x) t
    | x `Set.member` tyUnis t -> return contradiction
    | otherwise               -> solvedWithSubgoals (x `is` view value t) [ Subgoal (Value t) ]

  TEq t1 t2@(_ :< TyUniValue x) -> reduce disambiguate (TEq t2 t1) -- handled by the above case

  TEq (_ :< TyUniPlain x) t
    | x `Set.member` tyUnis t -> return contradiction
    | otherwise               -> solved (x `is` view value t)

  TEq t1 t2@(_ :< TyUniPlain x) -> reduce disambiguate (TEq t2 t1) -- handled by the above case

  TEq t1 t2
    | (Just (n1, t1s), Just (n2, t2s)) <- (unapplyTyCon t1, unapplyTyCon t2) ->
      if n1 == n2
        then return $ subgoals (zipWith (\t1 t2 -> Subgoal (TEq t1 t2)) t1s t2s)
        else return contradiction

  TEq (_ :< TyPair s1 s2) (_ :< TyPair t1 t2) -> return $ subgoals [ Subgoal (TEq s1 t1), Subgoal (TEq s2 t2) ]

  TEq (_ :< TyFn t1 t2) (_ :< TyFn s1 s2) -> return $ subgoals [ Subgoal (TEq t1 s1), Subgoal (TEq t2 s2) ]

  TEq t1'@(_ :< TyApplyOp _ _) t2' -> do
    let
      (op1, t1) = splitTyOp t1'
      (op2, t2) = splitTyOp t2'
    let
      split = subgoals [ Subgoal (TEq t1 t2), Subgoal (TEqIfAffine op1 op2 t1) ]
    if disambiguate
      then return split
      else case (view value t1, view value t2) of
        (TyUniPlain _, _) -> return skip
        (_, TyUniPlain _) -> return skip
        _                 -> return split

  TEq t1 t2@(_ :< TyApplyOp _ _) -> reduce disambiguate (TEq t2 t1) -- handled by the above case

  TEqIfAffine op1 op2 t -> do
    affine <- isAffine t
    case affine of
      No      -> return tautology
      Unknown -> return skip
      _       -> return $ subgoals [ Subgoal (TEq op1 op2) ]

  TEq op1@(_ :< TyOpUniView x) op2 -> do
    op2' <- normalize $ contractTyOps $ Set.delete op1 (expandTyOps op2)
    solved (x `is` view value op2')

  TEq op1 op2@(_ :< TyOpUniView _) -> return $ subgoals [ Subgoal (TEq op2 op1) ] -- handled by the above case

  TEq op1@(_ :< TyOpUniRef x) op2 -> do
    op2' <- normalize $ contractTyOps $ Set.delete op1 (expandTyOps op2)
    solvedWithSubgoals (x `is` (view value op2')) [ Subgoal (Ref op1) ]

  TEq op1 op2@(_ :< TyOpUniRef _) -> return $ subgoals [ Subgoal (TEq op2 op1) ] -- handled by the above case

  TEq op1@(_ :< TyOpIdentity) op2 -> do
    case isRef op2 of
      Yes -> return contradiction
      Variable -> return contradiction
      _ -> do
        let viewUnis = [ (x, TyOpIdentity) | (_ :< TyOpUniView x) <- Set.toList (expandTyOps op2) ]
        solved (are viewUnis)

  TEq op1 op2@(_ :< TyOpIdentity) -> return $ subgoals [ Subgoal (TEq op2 op1) ] -- handled by the above case

  Ref op -> do
    case isRef op of
      Yes     -> return tautology
      Unknown -> return skip
      _       -> return contradiction

  Value (_ :< t) -> case t of
    TyApplyOp op t -> do
      affine <- isAffine t
      case affine of
        Unknown  -> return skip
        No       -> error "unnormalized"
        _        -> return $ subgoals [ Subgoal (TEq op (phantom TyOpIdentity)), Subgoal (Value t) ]
    TyVarPlain _             -> return contradiction
    TyUniPlain _             -> return skip
    _                        -> return tautology

  RefFree refLabel t
    | Set.null (tyUnis t)
      -> if refLabel `Set.member` refLabels t then return contradiction else return tautology
    | otherwise
      -> return skip

  Instance (a0 :< inst) -> case inst of

    TyApply (_ :< TyCon "Integral") t | disambiguate
      -> return $ subgoals [ Subgoal (TEq t (TyCon "I32" `as` phantom KindType)) ]

    TyApply (a1 :< TyCon cls) t -> case view value t of
      TyApplyOp op t -> do
        let
          instVal = Instance (a0 :< TyApply (a1 :< TyCon cls) t)
          instRef = Instance (a0 :< TyApply (a1 :< TyCon cls) (phantom (TyApply (phantom (TyCon "Ref")) t)))
        affine <- isAffine t
        case (isRef op, affine) of
          (No, _)         -> error "unnormalized"
          (_, No)         -> error "unnormalized"
          (_, Unknown)    -> return skip
          (Unknown, _)    -> return skip
          (Yes, Yes)      -> reduceTyConInstance cls "Ref" [t]
          (Yes, Variable) -> return $ subgoals [ Subgoal instRef, copy t `Implies` instVal ]
          (Variable, _)   -> return $ subgoals [ Subgoal instRef, Subgoal instVal ]
      TyPair t1 t2 -> reduceTyConInstance cls "Pair" [t1, t2]
      TyFn t1 t2 -> reduceTyConInstance cls "Fn" [t1, t2]
      TyUnit -> reduceTyConInstance cls "Unit" []
      TyVarPlain _ -> return contradiction
      TyVarValue _ -> return contradiction
      _ | Just (n, ts) <- unapplyTyCon t -> reduceTyConInstance cls n ts
      _ -> return skip

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
    _             -> return skip
    where
      checkBounds :: forall a. (Integral a, Bounded a) => Integer -> a -> Praxis (Reduction TyConstraint)
      checkBounds n _ = if toInteger (minBound :: a) <= n && n <= toInteger (maxBound :: a) then return tautology else return contradiction

  _ -> return contradiction


  where
    reduceTyConInstance :: Name -> Name -> [Annotated Type] -> Praxis (Reduction TyConstraint)
    reduceTyConInstance cls name args = do
      l <- use iEnv
      let Just instances = Env.lookup name l
      case Map.lookup cls instances of
        Just resolver -> case resolver args of
          (_, IsInstance)          -> return tautology
          (_, IsInstanceOnlyIf cs) -> do
            cs <- mapM (\c -> view value <$> normalize (phantom c)) cs
            return (subgoals (map Subgoal cs))
        Nothing                    -> return contradiction

    tyUnis :: forall a. Term a => Annotated a -> Set Name
    tyUnis = extract (embedMonoid f) where
      f x = case x of
        TyUniPlain n  -> Set.singleton n
        TyUniValue n  -> Set.singleton n
        TyOpUniRef n  -> Set.singleton n
        TyOpUniView n -> Set.singleton n
        _             -> Set.empty

    refLabels :: forall a. Term a => Annotated a -> Set Name
    refLabels = extract (embedMonoid f) where
      f = \case
        TyOpRef n -> Set.singleton n
        _         -> Set.empty


-- Rewrite helpers
solved :: Resolver -> Praxis (Reduction TyConstraint)
solved resolve = solvedWithSubgoals resolve []

-- note: assumption is the subgoals are not affected by the solution
solvedWithSubgoals :: Resolver -> [Subgoal TyConstraint] -> Praxis (Reduction TyConstraint)
solvedWithSubgoals resolve subgoals = do
  tEnv %%= traverse (LEnv.value (normalize . sub resolve))
  return (Progress (Just (resolve, normalize)) subgoals)

are :: [(Name, Type)] -> Resolver
are ops = embedSub f where
  f (a :< x) = case x of
    TyUniPlain n  -> case n `lookup` ops of { Just op -> Just (a :< op); Nothing -> Nothing }
    TyUniValue n  -> case n `lookup` ops of { Just op -> Just (a :< op); Nothing -> Nothing }
    TyOpUniRef n  -> case n `lookup` ops of { Just op -> Just (a :< op); Nothing -> Nothing }
    TyOpUniView n -> case n `lookup` ops of { Just op -> Just (a :< op); Nothing -> Nothing }
    _             -> Nothing

is :: Name -> Type -> Resolver
is n t = embedSub f where
  f (a :< x) = case x of
    TyUniPlain n'  -> if n == n' then Just (a :< t) else Nothing
    TyUniValue n'  -> if n == n' then Just (a :< t) else Nothing
    TyOpUniRef n'  -> if n == n' then Just (a :< t) else Nothing
    TyOpUniView n' -> if n == n' then Just (a :< t) else Nothing
    _              -> Nothing

-- TyOp helpers
splitTyOp :: Annotated Type -> (Annotated Type, Annotated Type)
splitTyOp ty = case view value ty of
  TyApplyOp op ty -> (op, ty)
  _               -> (phantom TyOpIdentity, ty)

expandTyOps :: Annotated Type -> Set (Annotated Type)
expandTyOps op = case view value op of
  TyOpMulti ops -> ops
  TyOpIdentity  -> Set.empty
  _             -> Set.singleton op

contractTyOps :: Set (Annotated Type) -> Annotated Type
contractTyOps ops = case Set.toList ops of
  []   -> phantom TyOpIdentity
  [op] -> op
  _    -> phantom (TyOpMulti ops)

-- Term normalizer (after a substitution is applied)
normalize :: Normaliser
normalize (a :< x) = case typeof x of

  IType -> case x of

    TyApplyOp op1 (_ :< TyApplyOp op2 ty) -> do
      let op = (view source op1 <> view source op2, Nothing) :< TyOpMulti (Set.fromList [op1, op2])
      normalize (a :< TyApplyOp op ty)

    TyApplyOp op ty -> do
      op <- normalize op
      ty <- normalize ty
      case view value op of
        TyOpIdentity -> return ty
        _            -> do
          affine <- isAffine ty
          case affine of
            No -> return $ ty
            _  -> return $ (a :< TyApplyOp op ty)

    TyOpMulti ops -> do
      ops <- mapM normalize (Set.toList ops)
      return $ (contractTyOps . Set.delete (phantom TyOpIdentity) . Set.unions . map expandTyOps) ops

    _ -> continue

  _ -> continue

  where
    continue = recurse normalize (a :< x)


data Truth = Yes | No | Variable | Unknown
  deriving Show

isRef :: Annotated Type -> Truth
isRef op = case view value op of
  TyOpIdentity  -> No
  TyOpMulti ops -> Set.fold (\op -> truthOr (isRef op)) No ops
  TyOpRef _     -> Yes
  TyOpUniRef _  -> Yes
  TyOpUniView _ -> Unknown
  TyOpVarRef _  -> Yes
  TyOpVarView _ -> Variable

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
      TyApplyOp op t -> truthAnd (truthNot (isRef op)) <$> isAffine t
      TyUniPlain _ -> return Unknown
      TyUniValue _ -> return Unknown
      TyVarPlain _ -> return Variable
      TyVarValue _ -> return Variable
      _ | Just (n, ts) <- unapplyTyCon (a :< t) -> isTyConAffine n ts
      _ -> throw (a :< t)

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
    defaultRef name = do
      ref <- freshRef
      warnAt src $ "underdetermined reference " <> quote (pretty name) <> ", defaulting to " <> quote (pretty ref)
      return (name, view value ref)

    defaultView name = do
      warnAt src $ "underdetermined view " <> quote (pretty name) <> ", defaulting to " <> quote (pretty (phantom TyOpIdentity))
      return (name, TyOpIdentity)

  defaultViews <- mapM defaultView (Set.toList (deepViewUnis term))
  defaultRefs <- mapM defaultRef (Set.toList (deepRefUnis term))

  let defaultTyOps = defaultViews ++ defaultRefs

  case defaultTyOps of
    [] -> return term
    _  -> do
      Progress (Just (resolve, normalize)) _ <- solved (are defaultTyOps)
      (normalize . sub resolve) term

  where
    deepTyUnis :: forall a. Term a => Annotated a -> Set Name
    deepTyUnis = deepExtract (embedMonoid f) where
      f = \case
        TyUniPlain n -> Set.singleton n
        TyUniValue n -> Set.singleton n
        _            -> Set.empty

    deepRefUnis :: forall a. Term a => Annotated a -> Set Name
    deepRefUnis = deepExtract (embedMonoid f) where
      f = \case
        TyOpUniRef n -> Set.singleton n
        _            -> Set.empty

    deepViewUnis :: forall a. Term a => Annotated a -> Set Name
    deepViewUnis = deepExtract (embedMonoid f) where
      f = \case
        TyOpUniView n -> Set.singleton n
        _             -> Set.empty


-- When we encounter a polymorphic function with constraints, we should add the constraints to the assumption set when type checking the body.
-- However, since the solver acts globally, the best we can do is add the constraints to the global assumption set.
-- We need to be extra careful about the constraints introduced (to avoid unsatisfiable constraints which cause bad global deductions),
-- in particular we require all of the constraints to only include the bound type variables at their leaves.
--
-- We also "expand" the assumptions, e.g. if there is an instance C t => D t, the the assumption D t should also include C t.

-- TODO handle references/views!
assumeFromQType :: [Annotated TyVar] -> [Annotated TyConstraint] -> Praxis ()
assumeFromQType boundVars constraints = mapM_ assumeConstraint constraints where

  assumeConstraint :: Annotated TyConstraint -> Praxis ()
  assumeConstraint constraint = do
    constraint <- normalize constraint
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
        TyVarPlain _ -> return []
        TyVarValue _ -> return []
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

  checkConstraint :: Annotated TyConstraint -> Praxis ()
  checkConstraint constraint = case view value constraint of
    Instance (_ :< TyApply _ ty) -> checkConstraintType ty where
      checkConstraintType :: Annotated Type -> Praxis ()
      checkConstraintType (a@(src, _) :< ty) = case ty of
        TyPair t1 t2
          -> checkConstraintType t1 >> checkConstraintType t2
        TyFn t1 t2
          -> checkConstraintType t1 >> checkConstraintType t2
        TyVarPlain n | n `elem` Set.fromList (map tyVarName boundVars)
          -> return ()
        TyVarValue n | n `elem` Set.fromList (map tyVarName boundVars)
          -> return ()
        _ | Just (n, ts@(_:_)) <- unapplyTyCon (a :< ty)
          -> mapM_ checkConstraintType ts
        _
          -> throwAt src $ "illegal constraint: " <> pretty constraint
        -- TODO RefVar and ViewVar ?
