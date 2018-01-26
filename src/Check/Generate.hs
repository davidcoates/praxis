module Check.Generate
  ( generate
  ) where

import qualified Parse.AST as Parse

import Check.Derivation
import Check.Error
import Check.Env
import Check.AST
import Pos
import AST
import Type
import Prelude hiding (error)
import Control.Exception.Base (assert)
import Inbuilts
import Compile

contextJoin :: Pos -> Env -> Env -> Env -> (Env, [Derivation])
contextJoin p [] [] [] = ([],[])
contextJoin p ((x,(xt,xi)):xs) ((y,(yt,yi)):ys) ((z,(zt,zi)):zs) =
  assert ((x,xt) == (y,yt) && (y,yt) == (z,zt)) r
  where (l, c1)  = ((x,(xt,max yi zi)), if (xi == yi) == (yi == zi) then [] else [newDerivation (dropC xt) "Env join" p])
        (ls, c2) = contextJoin p xs ys zs
        r = (l:ls, c1 ++ c2)


generate :: Compiler TypeError [Derivation]
generate = set stage Generate >> generateExp

generateExp :: Compiler TypeError [Derivation]
generateExp = do
  t <- freshTyUni
  Just e <- get desugaredAST
  l <- get tEnv
  (e', l', cs) <- ge (l, e, pureTy t)
  set tEnv l'
  set typedAST (Just e')
  return cs

-- TODO: Effects
ge :: (Env, Parse.Annotated Exp, Type) -> Compiler TypeError (Annotated Exp, Env, [Derivation])
ge (l1, e, t) = ge' e
  where 
        ge' (Lit p x) = return (Lit (t, p) x, l1, [newDerivation (Sub t' t) ("Literal " ++ show x) p])
          where t' = case x of { Integer _ -> intTy ; Bool _ -> boolTy }
        
        ge' (If p a b c) = do
          (a', l2, c1) <- ge (l1, a, boolTy)
          (b', l3, c2) <- ge (l2, b, t)
          (c', l3',c3) <- ge (l2, c, t)
          let (l4, c4) = contextJoin p l2 l3 l3'
          return (If (t, p) a' b' c', l4, c1 ++ c2 ++ c3 ++ c4)

        ge' (Var p s) = do
          (t', l2, c1) <- use p s l1
          return (Var (t, p) s, l2, newDerivation (Sub (pureTy t') t) ("Variable " ++ s) p:c1)

        ge' (Apply p f x) = do
          a  <- freshTyUni
          (f', l2, c1) <- ge (l1, f, pureTy (TyFun a t) )
          (x', l3, c2) <- ge (l2, x, pureTy a)
          return (Apply (t, p) f' x', l3, c1 ++ c2)

-- |captures e returns a list of all free variables in e.
-- This is used to ensure functions don't capture linear variables.
-- There is a slight difference between captures and used free variables,
-- specifically for read-only references.
-- E.g., In "let x! in y", only y is used, but both x and y are captured.
captures :: Exp a -> [Name]
captures = undefined
