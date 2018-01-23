module Checker.Solver
  ( solve
  ) where

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

error :: TConstraint -> TypeError
error t = Error { pos = position t, stage = "inference(solver)", message = Contradiction t }


solve :: [TConstraint] -> TC [(String, Pure)]
solve [] = return []
solve (x:xs) = do
  (cs, subs) <- solve' x
  let ft x = lookup x subs
  let fe = const undefined
  subs' <- solve (cs ++ map (\c -> c { constraint = subsConstraint ft fe (constraint c) } ) xs)
  return (subs ++ subs')


occurs :: Pure -> Pure -> Bool
occurs t1 t2 = t1 == t2 || occurs' t2
  where occurs' (TyPrim _)    = False
        occurs' (TyUni _)     = False
        occurs' (TyFun a b)   = occurs t1 a || occursT t1 b
        occurs' (TyData _ ts) = any (occurs t1) ts
        occurs' (TyVar _)     = False

        occursT t1 (Ty t2 es) = occurs t1 t2


solve' :: TConstraint -> TC ([TConstraint], [(String, Pure)])
solve' TConstraint { constraint = Top }    = return ([],[])
solve' c@TConstraint { constraint = Bottom}  = typeError (error c)
  -- TODO: Occurs check
solve' c@TConstraint { constraint = Sub (Ty t1 e1) (Ty t2 e2) } | null e1 && null e2 = solveSub t1 t2
  where solveSub (TyUni s1) (TyUni s2) | s1 == s2 = return ([],[])
        solveSub (TyUni s1) t2 = if occurs (TyUni s1) t2 then typeError (error c) else return ([], [(s1,t2)])
        solveSub t1 t2@(TyUni _) = solveSub t2 t1

        solveSub (TyFun t1 t2) (TyFun t3 t4) = return ([c `implies` Sub (pureTy t1) (pureTy t3), c `implies` Sub t2 t4], [])
        solveSub t1@(TyFun _ _) t2 = contra t1 t2
        solveSub t1 t2@(TyFun _ _) = solveSub t2 t1

        solveSub t1@(TyPrim l1) t2@(TyPrim l2) | l1 == l2  = return ([],[])
                                               | otherwise = contra t1 t2

        solveSub t1 t2 = contra t1 t2

        contra t1 t2 = typeError (error (c `implies` (Sub (pureTy t1) (pureTy t2))))

solve' c@TConstraint {constraint = Class (Class.Constraint x (Ty t _)) } = do
  cs <- if x == "Share" || x == "Drop" then sd t else typeError (error c)
  return (cs, [])
    where sd :: Pure -> TC [TConstraint]
          sd (TyPrim _)  = return []
          sd (TyUni _)   = return [c]
          sd (TyFun _ _) = return []
          -- Rest is TODO

