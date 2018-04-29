module Check.Generate
  ( generate
  ) where

import qualified Parse.Parse.AST as Parse

import Check.Derivation
import Check.Env
import Check.AST
import Source
import AST
import Type
import Tag
import Control.Exception.Base (assert)
import Inbuilts hiding (ty)
import Compiler
import Error

contextJoin :: Source -> Env -> Env -> Env -> (Env, [Derivation])
contextJoin _ [] [] [] = ([],[])
contextJoin s ((x,(xt,xi)):xs) ((y,(yt,yi)):ys) ((z,(zt,zi)):zs) =
  assert ((x,xt) == (y,yt) && (y,yt) == (z,zt)) r
  where (l, c1)  = ((x,(xt,max yi zi)), if (xi == yi) == (yi == zi) then [] else [newDerivation (dropC xt) "Env join" s])
        (ls, c2) = contextJoin s xs ys zs
        r = (l:ls, c1 ++ c2)

generate :: Compiler [Derivation]
generate = do
  set stage Generate
  p <- get desugaredAST
  l <- get tEnv
  (l', p', cs) <- gp (l, p)
  set tEnv l'
  set typedAST p'
  debugPrint p'
  debugPrint cs
  return cs

ty :: Annotated Exp -> (Pure, Effects)
ty ((p :# e, _) :< _) = (p, e)

gp :: (Env, Parse.Annotated Program) -> Compiler (Env, Annotated Program, [Derivation])
gp = error "TODO: gp in Generate.hs"

ge :: (Env, Parse.Annotated Exp) -> Compiler (Env, Annotated Exp, [Derivation])
ge (l1, e) = ($ e) $ rec $ \s x -> case x of

  Lit x -> do
    let p = litTy x -- TODO polymorphic literals
    return (l1, (p :# empty, s) :< Lit x, [])

  If a b c -> do
    (l2, a', c1) <- ge (l1, a)
    (l3, b', c2) <- ge (l2, b)
    (l3', c', c3) <- ge (l2, c)
    let (l4, c4) = contextJoin s l2 l3 l3'
    let (ap, ae) = ty a'
    let (bp, be) = ty b'
    let (cp, ce) = ty c'
    let c5 = [ newDerivation (EqualP ap (TyPrim TyBool)) "condition of if expression must be Bool" s, newDerivation (EqualP bp cp) "branches of if expression must have the same type" s ]
    let e = unions [ae, be, ce]
    return (l4, (bp :# e, s) :< If a' b' c', c1 ++ c2 ++ c3 ++ c4 ++ c5)

  Var n -> do
    (p, l2, c1) <- use s n l1
    return (l2, (p :# empty, s) :< Var n, c1)

  Apply f x -> do
    yp :# ye  <- freshUniT
    (l2, f', c1) <- ge (l1, f)
    (l3, x', c2) <- ge (l2, x)
    let (fp, fe) = ty f'
    let (xp, xe) = ty x'
    let c3 = [ newDerivation (EqualP fp (TyFun xp (yp :# ye))) "fun app" s ]
    let e = unions [fe, xe, ye]
    return (l3, (yp :# e, s) :< Apply f' x', c1 ++ c2 ++ c3)

  Let n a b -> do
    (l2, a', c1) <- ge (l1, a)
    let (ap, ae) = ty a'
    (l3, b', c2) <- ge (intro (n, ap) l2, b)
    let (l4, c3) = elim s l3
    let (bp, be) = ty b'
    return (l4, (bp :# unions [ae, be], s) :< Let n a' b', c1 ++ c2 ++ c3)

  LetBang n a -> do
    (p, c1) <- readUse s n l1
    (l2, a', c2) <- ge (intro (n, TyBang p) l1, a)
    return (l2, a', c1 ++ c2)

  Signature a (sp :# se) -> do
    (l2, a', c1) <- ge (l1, a)
    let (ap, ae) = ty a'
    let c2 = [ newDerivation (EqualP sp ap) "user-supplied signature" s, newDerivation (EqualE se ae) "user-supplied signature" s ]
    return (l2, a', c1 ++ c2)

{- |Captures e returns a list of all free variables in e.
   This is used to ensure functions don't capture linear variables.
   There is a slight difference between captures and used free variables,
   specifically for read-only references.
   E.g., In "let x! in y", only y is used, but both x and y are captured.
-}
captures :: Exp a -> [Name]
captures = undefined
