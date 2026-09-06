-- | Structural instance resolution, shared by the type solver (via 'isAffine') and later stages (via 'isInstance').
--
-- The solver additionally reduces instance constraints in to subgoals (to drive unification); this module only answers
-- whether a type is an instance given what is currently known.
module Check.Type.Instance
  ( Truth(..)
  , truthAnd
  , truthNot
  , truthOr
  , isRef
  , resolveInstance
  , isInstance
  , unapplyTypeCon
  ) where

import           Check.State
import           Common
import           Print           ()
import           Stage
import           Term

import           Data.List       (foldl')
import qualified Data.Map.Strict as Map
import           Data.Set        (Set)
import qualified Data.Set        as Set


data Truth = Yes | No | Variable | Unknown
  deriving (Eq, Show)

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

-- | @truthIf c a b@ is @a@ if @c@ holds and @b@ if it does not.
truthIf :: Truth -> Truth -> Truth -> Truth
truthIf Yes a _ = a
truthIf No _ b  = b
truthIf c a b
  | a == b                       = a
  | Unknown `elem` [c, a, b]     = Unknown
  | otherwise                    = Variable

-- | Whether a type operator is a reference (as opposed to the identity).
isRef :: Annotated TypeCheck Type -> Truth
isRef op = case view value op of
  TypeIdentityOp -> No
  TypeRef _      -> Yes
  TypeSetOp ops  -> foldr (\op -> truthOr (isRef op)) No ops
  TypeUni Ref _  -> Yes
  TypeUni View _ -> Unknown
  TypeVar Ref _  -> Yes
  TypeVar View _ -> Variable
  _              -> error ("isRef: unexpected type operator " ++ fold (pretty op))

-- | Decompose a type application chain into its head constructor and arguments.
unapplyTypeCon :: Annotated s Type -> Maybe (Name, [Annotated s Type])
unapplyTypeCon = go [] where
  go args (_ :< TypeApply f x) = go (x : args) f
  go args (_ :< TypeCon name)  = Just (name, args)
  go _    _                    = Nothing

-- | Resolve whether a type is an instance, from the instance environment and a set of assumed constraints.
-- The answer is 'Variable' for a type variable with no matching assumption, and 'Unknown' if a unification variable is involved.
-- Recursive data types are handled coinductively.
resolveInstance :: InstanceEnv -> Set (Annotated TypeCheck TypeConstraint) -> TypeInstance -> Annotated TypeCheck Type -> Truth
resolveInstance env assumptions = go Set.empty where

  go :: Set (TypeInstance, Annotated TypeCheck Type) -> TypeInstance -> Annotated TypeCheck Type -> Truth
  go seen cls ty
    | phantom (TypeIsInstance cls ty) `Set.member` assumptions = Yes
    | (cls, ty) `Set.member` seen = Yes
    | otherwise = case view value ty of
        TypeApplyOp op ty' -> truthIf (isRef op) (con (mkName "Ref") [ty']) (go seen cls ty')
        TypePair ty1 ty2   -> con (mkName "Pair") [ty1, ty2]
        TypeFn ty1 ty2     -> con (mkName "Fn") [ty1, ty2]
        TypeUnit           -> con (mkName "Unit") []
        TypeUni _ _        -> Unknown
        TypeVar _ _        -> Variable
        _ | Just (n, args) <- unapplyTypeCon ty -> con n args
        _ -> error ("resolveInstance: unexpected type " ++ fold (pretty ty))
    where
      seen' = Set.insert (cls, ty) seen
      con n args = case Map.lookup n env >>= Map.lookup cls of
        Nothing       -> No
        Just resolver -> case snd (resolver args) of
          IsInstance          -> Yes
          IsInstanceOnlyIf cs -> foldl' truthAnd Yes (map holds cs)
      holds c = case view value c of
        TypeIsInstance cls' ty' -> go seen' cls' ty'
        _                       -> error "resolveInstance: unexpected constraint"

-- | Whether a closed (monomorphic) type is an instance.
isInstance :: InstanceEnv -> TypeInstance -> Annotated TypeCheck Type -> Bool
isInstance env cls ty = resolveInstance env Set.empty cls ty == Yes
