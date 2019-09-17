{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Check.Type.Solve
  ( solve
  , eval
  ) where

import           Check.Type.Error
import           Check.Type.Require  hiding (affine, share)
import qualified Check.Type.Require  as Require (affine, share)
import           Check.Type.System
import           Common
import           Introspect
import           Praxis
import           Record
import           Stage               hiding (Unknown)
import           Term

import           Control.Applicative (liftA2)
import           Data.List           (foldl', nub, sort)
import           Data.Maybe          (fromMaybe)
import           Data.Set            (Set, union)
import qualified Data.Set            as Set

solve :: Praxis ([(Name, Type TypeAnn)], [(Name, TyOp TypeAnn)])
solve = save stage $ save our $ do
  stage .= TypeCheck Solve
  solve'
  ts <- use (our . sol)
  ops <- use (our . ops)
  return (ts, ops)

data State = Cold
           | Warm
           | Done

solve' :: Praxis State
solve' = spin `chain` stuck where
  chain :: Praxis State -> Praxis State -> Praxis State
  chain p1 p2 = p1 >>= \case
    Cold -> p2
    Warm -> solve'
    Done -> return Done
  stuck = do
    cs <- (nub . sort) <$> use (our . constraints)
    output $ separate "\n\n" cs
    throw Stuck

spin :: Praxis State
spin = use (our . constraints) <&> (nub . sort) >>= \case
  [] -> return Done
  cs -> do
    our . constraints .= []
    our . staging .= cs
    warm <- loop
    return $ if warm then Warm else Cold
  where
    loop = use (our . staging) >>= \case
        []     -> return False
        (c:cs) -> (our . staging .= cs) >> liftA2 (||) (smap eval >> progress c) loop

unis = extract (only f)
 where f (TyUni n) = [n]
       f _         = []

-- TODO use sets here?
classes :: [Name] -> [Typed TypeConstraint] -> Maybe [Typed Type]
classes ns cs = (\f -> concat <$> mapM f cs) $ \d -> case view value d of
  Class t     -> let ns' = unis t in if all (`elem` ns) ns' then Just [t] else if any (`elem` ns') ns then Nothing else Just []
  TEq t1 t2   -> if any (`elem` (unis t1 ++ unis t2)) ns then Nothing else Just []

data Resolution = Known Bool -- In general we can't deduce Known False because of the open world assumption. The exception is Share / Affine (and their consequents)
                | Unknown
                | Unknowable
                | ImpliedBy [TypeConstraint TypeAnn]
  deriving (Eq, Ord)

-- TODO need proper instance solver
resolve :: Typed Type -> Praxis Resolution
resolve t = case view value t of

  TyApply (_ :< TyCon "Share") t  -> share t

  TyApply (_ :< TyCon "Affine") t -> affine t


resolves :: Traversable t => Bool -> (Typed Type -> Praxis Resolution) -> (Typed Type -> TypeConstraint TypeAnn) -> t (Typed Type) -> Praxis Resolution
resolves p f c ts = foldl' (<>) (Known p) <$> series (fmap weaken ts) where
  weaken t = do
    r <- f t
    case r of
      Unknown -> return (ImpliedBy [c t])
      _       -> return r
  (<>) x y = case if x <= y then (x, y) else (y, x) of
    (Known p', r)                -> if p == p' then r else Known p'
    (Unknowable, _)              -> Unknowable
    (ImpliedBy xs, ImpliedBy ys) -> ImpliedBy (xs ++ ys)


-- TODO might want to provide a function excluded_middle :: (Share a => b) -> (Affine a => b) -> b

affine :: Typed Type -> Praxis Resolution
affine t = do
  s <- (shareImpl True t)
  a <- (shareImpl False t)
  case (s, a) of
    (Known p, Known q)       -> if p == q then error "share == affine" else return (Known q)
    (Unknowable, Unknowable) -> return (Known False) -- Open world assumption does NOT apply to Share / Affine
    (Unknown, Unknown)       -> return Unknown

share :: Typed Type -> Praxis Resolution
share t = do
  s <- (shareImpl True t)
  a <- (shareImpl False t)
  case (s, a) of
    (Known p, Known q)       -> if p == q then error "share == affine" else return (Known p)
    (Unknowable, Unknowable) -> return (Known False) -- Open world assumption does NOT apply to Share / Affine
    (Unknown, Unknown)       -> return Unknown

shareImpl :: Bool -> Typed Type -> Praxis Resolution
shareImpl p t = case view value t of

  TyOp (_ :< op) t'
    | TyOpBang  <- op -> return (Known p)
    | TyOpUni _ <- op -> do
      r <- shareImpl p t'
      return $ case r of
        Known p' | p == p' -> Known p'
        _                  -> Unknown

  TyFun _ _  -> return (Known p)

  TyRecord r -> resolves p (shareImpl p) (if p then Require.share else Require.affine) r

  TyCon n
    | n `elem` ["Int", "Char", "Bool"] -> return (Known p)

  -- FIXME make this general!
  TyApply (_ :< TyCon "List") _ -> return (Known (not p))

  -- TODO derivations??
  TyVar n -> do
    axs <- fmap (view value) <$> use (our . axioms)
    let s = Require.share t `elem` axs
    let a = Require.affine t `elem` axs
    case (s, a) of
      (True, False)  -> return (Known True)
      (False, True)  -> return (Known False)
      (False, False) -> return Unknowable
      (True, True)   -> throw (ShareAffine t)

  _ -> return Unknown


progress :: Typed TypeConstraint -> Praxis Bool
progress d = case view value d of

  Class t -> do
    r <- resolve t
    case r of
      Known False  -> contradiction
      Known True   -> tautology
      Unknown      -> defer
      ImpliedBy ts -> introduce ts

  TEq t1 t2 | t1 == t2 -> tautology

  TEq (_ :< TyUni x) t -> if x `elem` unis t then contradiction else x `is` view value t
  TEq _ (_ :< TyUni _) -> swap

  TEq (_ :< TyApply n1 t1) (_ :< TyApply n2 t2) | n1 == n2  -> introduce [ TEq t1 t2 ]

  TEq (_ :< TyRecord r1) (_ :< TyRecord r2) | sort (keys r1) == sort (keys r2) ->
    let values = map snd . Record.toCanonicalList in introduce (zipWith TEq (values r1) (values r2)) -- TODO create zipRecord or some such

  TEq (_ :< TyFun t1 t2) (_ :< TyFun s1 s2) -> introduce [ TEq t1 s1, TEq t2 s2 ]

  TEq t1@(_ :< TyFlat e1) t2@(_ :< TyFlat e2)
    | e1 > e2 -> swap
    | [_ :< TyUni n] <- Set.toList e1 -> if n `elem` unis t2 then defer else n `is` view value t2
    | []             <- Set.toList e1 -> let empty (_ :< TyUni n) = n `is` TyFlat Set.empty
                                             empty _              = contradiction
                                         in foldr (\a b -> empty a >> b) solved e2
    | Just ((n1, l1), (n2, l2)) <- liftA2 (,) (snake e1) (snake e2) ->
        if n1 == n2 then do
          a <- freshTyUni
          n1 `is` TyFlat (Set.unions [Set.singleton a, Set.difference l2 l1, Set.difference l1 l2])
        else
          n1 `is` TyFlat (Set.union (Set.difference l2 l1) (Set.singleton (TyUni n2 `as` phantom KindType)))
    | Just (n1, l1) <- snake e1 ->
        if literals e2 then
          if Set.isSubsetOf l1 e2 then
            defer
            -- FIXME This isn't correct! We could add any subset of l1 to n1
            -- solve n1 (TyFlat (Set.difference e2 l1)) -- TODO for all these differences, need to flatten?
          else
            contradiction
        else
          defer
    | null (unis t1 ++ unis t2) -> contradiction
    | otherwise                     -> defer

  TEq (_ :< TyOp (_ :< TyOpUni n1) t1) (_ :< TyOp (_ :< TyOpUni n2) t2) | n1 == n2 -> introduce [ TEq t1 t2 ]

  TEq (_ :< TyOp (_ :< op) t1) t2 -> do
    s1 <- share t1
    s2 <- share t2
    case (op, s1, s2, viewFree t2) of
      (TyOpUni _, _, Known True, True)         -> introduce [ TEq t1 t2 ]
      (TyOpUni n, Known False, Known False, _) -> n `isView` False >> introduce [ TEq t1 t2 ]
      (TyOpUni n, Known False, Known True, _)  -> n `isView` True
      _ -> defer

  TEq _ (_ :< TyOp _ _) -> swap

  _ -> contradiction

  where solved = return True
        tautology = solved
        defer = require d >> return False
        contradiction = throw (Contradiction d)
        introduce cs = requires (map (d `implies`) cs) >> return True
        swap = case view value d of t1 `TEq` t2 -> progress (set value (t2 `TEq` t1) d)

        snake :: Set (Typed Type) -> Maybe (Name, Set (Typed Type))
        snake es = case Set.toList es of
          ((_ :< TyUni n):es) -> if null (concatMap unis es) then Just (n, Set.fromList es) else Nothing
          _                   -> Nothing

        literals :: Set (Typed Type) -> Bool
        literals es = null (concatMap unis (Set.toList es))

        viewFree :: Typed Type -> Bool
        viewFree t = case view value t of
          TyUni _ -> False
          TyOp (_ :< op) t -> case op of
            TyOpBang  -> False
            TyOpUni _ -> False
            TyOpId    -> viewFree t
          _ -> True


smap :: (forall a. Recursive a => Typed a -> Praxis (Typed a)) -> Praxis ()
smap f = do
  let lower :: (Typed Type -> Praxis (Typed Type)) -> Type TypeAnn -> Praxis (Type TypeAnn)
      lower f x = view value <$> f (x `as` phantom KindType)
  our . sol %%= traverse (second (lower f))
  our . constraints %%= traverse f
  our . staging %%= traverse f
  our . axioms %%= traverse f
  tEnv %%= traverse f
  return ()

isView :: Name -> Bool -> Praxis Bool
isView n b = do
  let op = if b then TyOpBang else TyOpId
  smap $ pure . sub (\case { TyOpUni n' | n == n' -> Just op; _ -> Nothing })
  our . ops %= ((n, op):)
  return True

is :: Name -> Type TypeAnn -> Praxis Bool
is n t = do
  smap $ pure . sub (\case { TyUni n' | n == n' -> Just t; _ -> Nothing })
  our . sol %= ((n, t):)
  reuse n
  return True

eval :: forall a. Recursive a => Typed a -> Praxis (Typed a)
eval x = introspect (just f) x where
  f :: Typed Type -> Visit Praxis () (Type TypeAnn)
  f (a :< t) = case t of
    TyOp (_ :< TyOpId) t -> Resolve (view value <$> eval t)
    TyOp (a :< op) t -> Resolve $ do
      t' <- eval t
      r <- share t'
      return $ case r of
        Known True -> view value t'
        _          -> TyOp (a :< op) t'
    _ -> skip
