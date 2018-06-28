{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Check.Solve
  ( solve
  ) where

import Check.Derivation
import AST
import Type
import Prelude hiding (error)
import Data.Maybe (fromJust)
import Text.Parsec.Pos (newPos)
import qualified Data.Set as Set
import Data.List (nub)
import Compiler
import Error
import Record

-- TODO: Make system part of Compiler state?
-- TODO: Batch all effect constraints (or treat them as check?)
--    so progress -> effects -> check

data System = System
  { vars     :: [(Name, Pure)]
  , progress :: [Derivation]
  , check    :: [Derivation]
  }

data UniType = UniTy | UniEf

class Unis a where
  unis :: UniType -> a -> [Name]

  tyUnis :: a -> [Name]
  tyUnis = unis UniTy
  efUnis :: a -> [Name]
  efUnis = unis UniEf
  allUnis :: a -> [Name]
  allUnis x = tyUnis x ++ efUnis x

instance Unis Derivation where
  unis s d = unis s (constraint d)

instance Unis Constraint where
  unis s (EqualP p1 p2) = unis s p1 ++ unis s p2
  unis s (EqualE e1 e2) = unis s e1 ++ unis s e2
  unis s (Class _ t)    = unis s t 

instance Unis Type where
  unis s (t :# e) = unis s t ++ unis s e

instance Unis Effect where
  unis UniEf (EfUni n) = [n]
  unis _     _         = []

instance Unis Effects where
  unis s = concat . Set.elems . Set.map (unis s)

instance Unis Pure where
  unis s (TyFun t1 t2) = unis s t1 ++ unis s t2
  unis s (TyData _ ts) = concatMap (unis s) ts
  unis s (TyRecord r)  = concatMap (unis s) r
  unis s (TyBang p)    = unis s p
  
  unis UniTy (TyUni n) = [n]
  unis _     (TyUni _) = []

  unis s (TyVar _)     = []
  unis s TyUnit        = []
  unis s (TyPrim _)    = []

solve :: [Derivation] -> Compiler [(String, Pure)]
solve xs = setIn stage Solve $ do
  let s = System { vars = map (\t -> (t, TyUni t)) (nub (concatMap allUnis xs)), progress = filter isProgress xs, check = filter isCheck xs }
  s <- solveProgress s
  verifyProgressComplete s
  verifyCheck s
  debugPrint (vars s)
  return (vars s)
    where isProgress d = case constraint d of { EqualP _ _ -> True; EqualE _ _ -> True;  _ -> False }
          isCheck = not . isProgress

-- |Checks all EqualP constraints are of the form uni ~ concrete 
-- TODO Check effects also
verifyProgressComplete :: System -> Compiler ()
verifyProgressComplete s = mapM_ ok (progress s)
  where ok d = case constraint d of
          EqualP (TyUni _) p -> if null (tyUnis p) then pure () else underdefined d -- TODO need a different error? (internal error? or underdefined?)
          EqualP _         _ -> underdefined d -- TODO this shouldn't happen? better error messsage?
          _                  -> pure ()

-- |occurs t1 t2 returns True iff t1 is contained within t2
occurs :: Pure -> Pure -> Bool
occurs t1 t2 = t1 == t2 || occurs' t2
  where occurs' (TyPrim _)    = False
        occurs' (TyUni _)     = False
        occurs' (TyFun a b)   = occurs t1 a || occursT t1 b
        occurs' (TyData _ ts) = any (occurs t1) ts
        occurs' (TyVar _)     = False
        occurs' (TyRecord r)  = or (fmap (occurs t1) r)
        occurs' TyUnit        = False
        occurs' (TyBang p)    = occurs t1 p
        occursT t1 (t2 :# es) = occurs t1 t2


-- |Applies a substitution to the system.
-- Does NOT perform occurs check
sub :: (Name, Pure) -> System -> System
sub (n,t) s = s{ vars = vars', progress = progress', check = check' }
  where ft x = lookup x [(n,t)]
        fe x = lookup x [] -- TODO ?
        vars' = map (\(n,t) -> (n, subsPure ft fe t)) (vars s)
        subsD = \d -> d { constraint = subsConstraint ft fe (constraint d) }
        progress' = map subsD (progress s)
        check'    = map subsD (check s)

contradiction :: Derivation -> Compiler a
contradiction = throwError . CheckError . Contradiction

underdefined :: Derivation -> Compiler a
underdefined = throwError . CheckError . Underdefined

solveProgress :: System -> Compiler System
solveProgress s@System { progress = [] } = return s
solveProgress s@System { progress = d:ds } = case constraint d of

  EqualP t1 t2 -> do
    s <- solveEqualP t1 t2
    solveProgress s
      where solveEqualP (TyUni s1) (TyUni s2) | s1 == s2 = return s{ progress = ds }
            solveEqualP (TyUni s1) t2 = if occurs (TyUni s1) t2 then contradiction d else return $ sub (s1,t2) s{ progress = ds }
            solveEqualP t1 t2@(TyUni _) = solveEqualP t2 t1

            solveEqualP (TyFun t1 (t2 :# e2)) (TyFun t3 (t4 :# e4)) = return s{ progress = d `implies` EqualP t1 t3 : d `implies` EqualP t2 t4 : d `implies` EqualE e2 e4 : ds }
            solveEqualP t1@(TyFun _ _) t2 = contra t1 t2
            solveEqualP t1 t2@(TyFun _ _) = solveEqualP t2 t1

            solveEqualP t1@(TyPrim l1) t2@(TyPrim l2) | l1 == l2  = return s{ progress = ds }
                                                   | otherwise = contra t1 t2

            solveEqualP t1@(TyRecord r1) t2@(TyRecord r2) = let
              (r1', r2') = (toCanonicalList r1, toCanonicalList r2)
              keysEq = all (uncurry (==)) (zip (map fst r1') (map fst r2'))
              ds' = map (\(p1, p2) -> d `implies` EqualP p1 p2) $ zip (map snd r1') (map snd r2')
                in if keysEq then return s{ progress = ds' ++ ds } else contra t1 t2

            solveEqualP TyUnit TyUnit = return s{ progress = ds }

            solveEqualP t1 t2 = contra t1 t2

            contra t1 t2 = contradiction (d `implies` EqualP t1 t2)

  EqualE e1 e2 -> do -- TODO
    s <- solveEqualE e1 e2
    solveProgress s
      where solveEqualE e1 e2 | e1 == empty && e2 == empty = return s{ progress = ds }
            solveEqualE e1 e2 = return s{ progress = ds } -- FIXME

verifyCheck :: System -> Compiler ()
verifyCheck s@System { check = [] } = return ()
verifyCheck s@System { check = d:ds } = case constraint d of
  Class x t -> do
    if x == "Share" || x == "Drop" then sd t else contradiction d
    verifyCheck s{ check = ds }
      where sd :: Pure -> Compiler ()
            sd (TyPrim _)  = return ()
            sd (TyUni _)   = underdefined d
            sd (TyFun _ _) = return ()
            -- Rest is TODO

