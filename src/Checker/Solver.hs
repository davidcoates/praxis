module Checker.Solver
  ( solve
  ) where

import Checker.Constraint (Constraint(..))
import qualified Checker.Constraint as C (share, drop)
import Checker.TCMonad
import Checker.Constraint
import AST
import Type hiding (Constraint)
import qualified Type as Class (Constraint(..))
import Prelude hiding (error)
import Data.Maybe (fromJust)
import Checker.Error
import Text.Parsec.Pos (newPos)
import qualified Data.Set as Set (null)

error :: TypeErrorTy -> TypeError
error t = Error { pos = SourcePos (newPos "dummy" 0 0), stage = "inference(solver)", message = t }

solve :: [Constraint] -> TC [(String, Pure)]
solve [] = return []
solve (x:xs) = do
  (cs, subs) <- solve' x
  let ft x = lookup x subs
  let fe = const undefined
  subs' <- solve (cs ++ map (subsConstraint ft fe) xs)
  return (subs ++ subs')

solve' :: Constraint -> TC ([Constraint], [(String, Pure)])
solve' Top    = return ([],[])
solve' Bottom = typeError (error (Contradiction Bottom))
  -- TODO: Occurs check
solve' (Sub (Ty t1 e1) (Ty t2 e2)) | null e1 && null e2 = solveSub t1 t2
  where solveSub (TyUni s1) t2 = return ([], [(s1,t2)])
        solveSub t1 t2@(TyUni _) = solveSub t2 t1

        solveSub (TyFun t1 t2) (TyFun t3 t4) = return ([Sub (pureType t1) (pureType t3), Sub t2 t4], [])
        solveSub t1@(TyFun _ _) t2 = contra t1 t2
        solveSub t1 t2@(TyFun _ _) = solveSub t2 t1

        solveSub t1@(TyPrim l1) t2@(TyPrim l2) | l1 == l2  = return ([],[])
                                         | otherwise = contra t1 t2

        solveSub t1 t2 = contra t1 t2

        contra t1 t2 = typeError (error (Contradiction (Sub (pureType t1) (pureType t2))))

solve' (Class c) = do
  cs <- solveClass c
  return (cs, [])

solveClass :: Class.Constraint -> TC [Constraint]
solveClass c@(Class.Constraint x (Ty t _)) = if x == "Share" || x == "Drop" then sd t else typeError (error (Contradiction (Class c)))
  where sd :: Pure -> TC [Constraint]
        sd (TyPrim _)  = return []
        sd (TyUni _)   = return [Class c]
        sd (TyFun _ _) = return []
        -- Rest is TODO
