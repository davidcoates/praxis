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
import Control.Exception.Base (assert)

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
           | Var String
           | Apply (a (Exp a)) (a (Exp a))
-}

{-

-}
contextJoin :: Context -> Context -> Context -> (Context, [Constraint])
contextJoin [] [] [] = ([],[])
contextJoin ((x,(xt,xi)):xs) ((y,(yt,yi)):ys) ((z,(zt,zi)):zs) =
  assert ((x,xt) == (y,yt) && (y,yt) == (z,zt)) r
  where (l, c1)  = ((x,(xt,max yi zi)), if (xi == yi) == (yi == zi) then [] else [C.drop (pureType xt)])
        (ls, c2) = contextJoin xs ys zs
        r = (l:ls, c1 ++ c2)

generateExp :: Annotate SourcePos Exp -> TC (Annotate (Type, SourcePos) Exp, [Constraint])
generateExp e = do
  t <- freshTyUni
  (e', _, cs) <- generateExp' (topContext, e, pureType t)
  return (e', cs)


generateExp' :: (Context, Annotate SourcePos Exp, Type) -> TC (Annotate (Type, SourcePos) Exp, Context, [Constraint])
generateExp' (l1, p :< e, t) = (\(e', l2, cs) -> ((t,p) :< e', l2, cs)) <$> exp l1 t e
  where exp l1 t e = exp' e

        exp' (Lit x) = return (Lit x, l1, [Sub t' t])
          where t' = case x of { Integer _ -> intTy ; Bool _ -> boolTy }

        exp' (If a b c)        = do
          (a', l2, c1) <- generateExp' (l1, a, boolTy)
          (b', l3, c2)  <- generateExp' (l2, b, t)
          (c', l3', c3) <- generateExp' (l2, c, t)
          let (l4, c4) = contextJoin l2 l3 l3'
          return (If a' b' c', l4, c1 ++ c2 ++ c3 ++ c4)

        exp' (Var s) = do
          (t', l2, c1) <- use p s l1
          return (Var s, l2, (Sub (pureType t') t):c1)

        exp' (Apply _ _) = undefined
