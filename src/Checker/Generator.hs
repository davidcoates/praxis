module Checker.Generator
  ( generateExp
  ) where

import Checker.Constraint (Constraint(..))
import Checker.Error
import qualified Checker.Constraint as C (share, drop)
import Checker.TCMonad
import AST
import Type hiding (Constraint(..))
import qualified Type as T (Constraint(..))
import Prelude hiding (error)


error :: SourcePos -> TypeErrorTy -> TypeError
error p t = Error { pos = p, stage = "inference(generator)", message = t }

-- A Context stores all in-scope variables along with their type and how many times they are used.
-- This last datum is necessary to enforce linearity
type Context = [(String, (Pure, Int))]

-- Increment the usage count of a particular variable
inc :: String -> Context -> Context
inc s                [] = []
inc s (l@(s',(t,i)):ls) = if s == s' then (s',(t,i+1)):ls else l : inc s ls

-- Increment the usage count of a particular variable, and generate a Share constraint if it has already been used.
use :: SourcePos -> String -> Context -> TC (Pure, Context, [Constraint])
use p s l = case lookup s l of Just (t, i) -> pure (t, inc s l, if i == 0 then [] else [C.share (pureType t)])
                               Nothing     -> typeError (error p (NotInScope s))

intTy :: Type
intTy = pureType (TyPrim TyInt)

-- integerTy = pureType $ TyData "Integer" []

boolTy :: Type
boolTy = pureType (TyPrim TyBool)

topFuns = [("Prelude.+", TyFun (TyPrim TyInt) intTy)]

topContext :: Context
topContext = map (\(s, t) -> (s, (t,0))) topFuns

{-
data Exp a = If (a (Exp a)) (a (Exp a)) (a (Exp a))
           | Lit Lit
           | Fun String
           | Apply (a (Exp a)) (a (Exp a))
           | Prim Prim
-}


generateExp :: Annotate SourcePos Exp -> TC (Annotate (Type, SourcePos) Exp, [Constraint])
generateExp e = do
  t <- freshTyUni
  (e', _, cs) <- generateExp' (topContext, e, pureType t)
  return (e', cs)


generateExp' :: (Context, Annotate SourcePos Exp, Type) -> TC (Annotate (Type, SourcePos) Exp, Context, [Constraint])
generateExp' (l1, p :< e, t) = (\(e', l2, cs) -> ((t,p) :< e', l2, cs)) <$> exp l1 t e
  where exp l1 t e = exp' e
        exp' (Lit (Integer i)) = pure $ (Lit (Integer i), l1, [Eq t intTy])

        exp' (If a b c)        = do
          (a', l2, c1) <- generateExp' (l1, a, boolTy)
          (b', l3, c2) <- generateExp' (l2, b, t)
          (c', l4, c3) <- generateExp' (l3, c, t)
          return (If a' b' c', l4, c1 ++ c2 ++ c3)

--        exp' (Fun s)          = let t' = fromJust (lookup s l1)
