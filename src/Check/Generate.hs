module Check.Generate
  ( generate
  ) where

import qualified Parse.Parse.AST as Parse

import Check.Derivation
import Check.Error
import Check.Env
import Check.AST
import Source
import AST
import Type
import Tag
import Prelude hiding (error)
import Control.Exception.Base (assert)
import Inbuilts
import Compile

contextJoin :: Source -> Env -> Env -> Env -> (Env, [Derivation])
contextJoin _ [] [] [] = ([],[])
contextJoin s ((x,(xt,xi)):xs) ((y,(yt,yi)):ys) ((z,(zt,zi)):zs) =
  assert ((x,xt) == (y,yt) && (y,yt) == (z,zt)) r
  where (l, c1)  = ((x,(xt,max yi zi)), if (xi == yi) == (yi == zi) then [] else [newDerivation (dropC xt) "Env join" s])
        (ls, c2) = contextJoin s xs ys zs
        r = (l:ls, c1 ++ c2)


generate :: Compiler TypeError [Derivation]
generate = set stage Generate >> generateExp

generateExp :: Compiler TypeError [Derivation]
generateExp = do
  t <- freshTyUni
  e <- get desugaredAST
  l <- get tEnv
  (e', l', cs) <- ge (l, e, pureTy t)
  set tEnv l'
  set typedAST e'
  return cs

-- TODO: Effects
ge :: (Env, Parse.Annotated Exp, Type) -> Compiler TypeError (Annotated Exp, Env, [Derivation])
ge (l1, e, t) = ($ e) $ rec $ \s x -> case x of

  Lit x -> return ((t, s) :< Lit x, l1, [newDerivation (Sub t' t) ("Literal " ++ show x) s])
    where t' = case x of { Integer _ -> intTy ; Bool _ -> boolTy }

  If a b c -> do
    (a', l2, c1) <- ge (l1, a, boolTy)
    (b', l3, c2) <- ge (l2, b, t)
    (c', l3',c3) <- ge (l2, c, t)
    let (l4, c4) = contextJoin s l2 l3 l3'
    return ((t, s) :< If a' b' c', l4, c1 ++ c2 ++ c3 ++ c4)


  Var n -> do
    (t', l2, c1) <- use s n l1
    return ((t, s) :< Var n, l2, newDerivation (Sub (pureTy t') t) ("Variable " ++ n) s : c1)

  Apply f x -> do
    a  <- freshTyUni
    (f', l2, c1) <- ge (l1, f, pureTy (TyFun a t) )
    (x', l3, c2) <- ge (l2, x, pureTy a)
    return ((t, s) :< Apply f' x', l3, c1 ++ c2)

{- |Captures e returns a list of all free variables in e.
   This is used to ensure functions don't capture linear variables.
   There is a slight difference between captures and used free variables,
   specifically for read-only references.
   E.g., In "let x! in y", only y is used, but both x and y are captured.
-}
captures :: Exp a -> [Name]
captures = undefined
