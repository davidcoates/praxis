module Check.Solve
  ( solve
  ) where

import Check.Derivation
import Check.Error
import AST
import Type
import Prelude hiding (error)
import Data.Maybe (fromJust)
import Check.Error
import Text.Parsec.Pos (newPos)
import qualified Data.Set as Set (null)
import Compiler

data System = System
  { vars     :: [(Name, Pure)]
  , progress :: [Derivation]
  , check    :: [Derivation]
  }

unis :: Derivation -> [Name]
unis d = unisC (constraint d)

unisC :: Constraint -> [Name]
unisC (Sub t1 t2) = unisT t1 ++ unisT t2
unisC (Class _ t) = unisP t


unisP :: Pure -> [Name]
unisP (TyFun t1 t2) = unisP t1 ++ unisT t2
unisP (TyData _ ts) = concatMap unisP ts
unisP (TyUni s)     = [s]
unisP _             = []

unisT :: Type -> [Name]
unisT (Ty t _) = unisP t

solve :: [Derivation] -> Compiler [(String, Pure)]
solve xs = do
  set stage Solve
  s <- solveProgress System { vars = map (\t -> (t, TyUni t)) (concatMap unis xs), progress = filter isProgress xs, check = filter isCheck xs }
  verifyCheck s
  debugPrint (vars s)
  return (vars s)
    where isProgress d = case constraint d of { Sub _ _ -> True; _ -> False }
          isCheck = not . isProgress

-- | occurs t1 t2 returns True iff t1 is contained within t2
occurs :: Pure -> Pure -> Bool
occurs t1 t2 = t1 == t2 || occurs' t2
  where occurs' (TyPrim _)    = False
        occurs' (TyUni _)     = False
        occurs' (TyFun a b)   = occurs t1 a || occursT t1 b
        occurs' (TyData _ ts) = any (occurs t1) ts
        occurs' (TyVar _)     = False
        occursT t1 (Ty t2 es) = occurs t1 t2

-- | Applies a substitution to the system.
-- | Does NOT perform occurs check
sub :: (Name, Pure) -> System -> System
sub (n,t) s = s{ vars = vars', progress = progress', check = check' }
  where ft x = lookup x [(n,t)]
        fe x = undefined
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
  Sub (Ty t1 e1) (Ty t2 e2) | null e1 && null e2 -> solveSub t1 t2
    where solveSub (TyUni s1) (TyUni s2) | s1 == s2 = return s{ progress = ds }
          solveSub (TyUni s1) t2 = if occurs (TyUni s1) t2 then contradiction d else return $ sub (s1,t2) s{ progress = ds }
          solveSub t1 t2@(TyUni _) = solveSub t2 t1

          solveSub (TyFun t1 t2) (TyFun t3 t4) = return s{ progress = d `implies` Sub (pureTy t1) (pureTy t3) : d `implies` Sub t2 t4 : ds }
          solveSub t1@(TyFun _ _) t2 = contra t1 t2
          solveSub t1 t2@(TyFun _ _) = solveSub t2 t1

          solveSub t1@(TyPrim l1) t2@(TyPrim l2) | l1 == l2  = return s{ progress = ds }
                                                 | otherwise = contra t1 t2

          solveSub t1 t2 = contra t1 t2

          contra t1 t2 = contradiction (d `implies` Sub (pureTy t1) (pureTy t2))

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

