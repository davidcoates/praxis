{-# LANGUAGE TypeFamilies #-}

-- | Linearization: make every variable be consumed exactly once on every path.
--
-- The type checker guarantees that an affine (non-Copy) variable is consumed at most once on any path, that a
-- Copy variable may be used any number of times, and that any variable which is not consumed on some path is
-- Drop. This pass makes copying and dropping explicit, by inserting calls to the @copy@ and @drop@
-- inbuilts, so that afterwards every use of a variable is a move:
--
--   * A use of a variable which is used again later on the same path becomes @copy x@.
--   * A path on which a variable is not used at all ends with @drop x@.
--
-- Hole patterns bind (unused) variables like any other pattern, so they are handled uniformly.
-- Uses of a variable within a read of that variable are uses of the reference, so do not consume it (though for a
-- copyable variable the reference is the variable itself).
--
-- Top-level (global) variables are not linearized: a global is immortal and immutable, and the type checker gives every
-- use of a global the type of a reference with a static lifetime, so globals are only ever read and never consumed.
module Lower.Linearize
  ( run
  , runExp
  ) where

import           Check.State         (instanceEnv)
import           Check.Type.Instance (isInstance)
import           Common
import           Introspect
import           Praxis
import           Stage
import           Term

import           Control.Monad       (foldM)
import           Control.Monad.State (StateT, evalStateT, get, put)
import           Control.Monad.Trans (lift)
import           Data.Monoid         (Any (..))


type Type' = Annotated TypeCheck Type

-- | Whether a type can be copied.
type IsCopy = Type' -> Bool


-- * Entry points

run :: Annotated Lower Program -> Praxis (Annotated Lower Program)
run (_ :< Program decls) = do
  isCopy <- isCopyFromEnv
  decls' <- mapM (linearizeDecl isCopy) decls
  let result = phantom (Program decls')
  display Lower "linearized program" result `ifFlag` debug
  return result

runExp :: Annotated Lower Exp -> Praxis (Annotated Lower Exp)
runExp exp = do
  isCopy <- isCopyFromEnv
  result <- linearizeExp isCopy exp
  display Lower "linearized exp" result `ifFlag` debug
  return result

isCopyFromEnv :: Praxis IsCopy
isCopyFromEnv = do
  env <- use (checkState . instanceEnv)
  return (isInstance env Copy)


-- * Declarations

linearizeDecl :: IsCopy -> Annotated Lower Decl -> Praxis (Annotated Lower Decl)
linearizeDecl isCopy (a :< decl) = (a :<) <$> case decl of
  DeclTerm dt -> DeclTerm <$> linearizeDeclTerm isCopy dt
  DeclRec ds  -> DeclRec <$> mapM linearizeDeclRec ds
  _           -> return decl
  where
    linearizeDeclRec (a :< dr) = (a :<) <$> case dr of
      DeclRecTerm dt -> DeclRecTerm <$> linearizeDeclTerm isCopy dt
      _              -> return dr

linearizeDeclTerm :: IsCopy -> Annotated Lower DeclTerm -> Praxis (Annotated Lower DeclTerm)
linearizeDeclTerm isCopy (a :< dt) = (a :<) <$> case dt of
  DeclTermVar name qTy body -> DeclTermVar name qTy <$> linearizeExp isCopy body
  _                         -> return dt


-- * Expressions

-- | Linearize every variable bound within the expression.
linearizeExp :: IsCopy -> Annotated Lower Exp -> Praxis (Annotated Lower Exp)
linearizeExp isCopy ((src, ty) :< exp) = ((src, ty) :<) <$> case exp of

  Lambda pat body -> Lambda pat <$> (go body >>= scope pat)

  Cases alts -> Cases <$> mapM alt alts

  Case scrut alts -> Case <$> go scrut <*> mapM alt alts

  Let (b :< Bind pat rhs) body -> do
    rhs'  <- go rhs
    body' <- go body >>= scope pat
    return (Let (b :< Bind pat rhs') body')

  _ -> recurseTerm child exp

  where
    go = linearizeExp isCopy

    alt (pat, body) = (pat,) <$> (go body >>= scope pat)

    -- The body is the scope of the variables bound by the pattern.
    scope :: Annotated Lower Pat -> Annotated Lower Exp -> Praxis (Annotated Lower Exp)
    scope pat body = foldM (\body (name, t) -> linearize isCopy name t body) body (patVars pat)

    child :: forall a. IsTerm a => Annotated Lower a -> Praxis (Annotated Lower a)
    child term = case typeof (view value term) of
      ExpT -> go term
      _    -> return term


-- | Rewrite the scope of a variable so that it is consumed exactly once on every path.
linearize :: IsCopy -> Name -> Type' -> Annotated Lower Exp -> Praxis (Annotated Lower Exp)
linearize isCopy x xTy = consume where

  copyable = isCopy xTy

  -- Whether the variable is used (on some path) within an expression.
  used :: Annotated Lower Exp -> Bool
  used = getAny . uses where
    uses :: forall a. IsTerm a => Annotated Lower a -> Any
    uses term = case typeof (view value term) of
      ExpT -> case view value term of
        Var y          -> Any (y == x)
        Read y body    -> if y == x && not copyable then Any False else uses body
        Closure caps _ -> Any (x `elem` map fst caps)
        exp            -> getConst (recurseTerm (Const . uses) exp)
      _ -> getConst (recurseTerm (Const . uses) (view value term))

  -- Precondition: the variable is owned. Postcondition: the variable is consumed exactly once on every path.
  consume :: Annotated Lower Exp -> Praxis (Annotated Lower Exp)
  consume e@((src, ty) :< exp)
    | not (used e) = return (dropAfter x xTy e)
    | otherwise = ((src, ty) :<) <$> case exp of

        Var _ -> return exp

        -- A captured variable is consumed by the closure
        Closure _ _ -> return exp

        Read y body -> Read y <$> consume body

        -- The variable is consumed by the branches if any of them uses it, otherwise by the condition
        If cond thenExp elseExp
          | used thenExp || used elseExp -> If <$> retain cond <*> consume thenExp <*> consume elseExp
          | otherwise                    -> (\cond -> If cond thenExp elseExp) <$> consume cond

        Case scrut alts
          | any (used . snd) alts -> Case <$> retain scrut <*> mapM (\(pat, body) -> (pat,) <$> consume body) alts
          | otherwise             -> (\scrut -> Case scrut alts) <$> consume scrut

        -- Conditions are evaluated in turn until one holds, so a switch is a nest of ifs
        Switch alts -> Switch <$> consumeSwitch alts

        Let (b :< Bind pat rhs) body
          | used body -> (\rhs body -> Let (b :< Bind pat rhs) body) <$> retain rhs <*> consume body
          | otherwise -> (\rhs -> Let (b :< Bind pat rhs) body) <$> consume rhs

        -- Everything else evaluates its children in order. The last child to use the variable consumes it.
        _ -> consumeLast exp

  consumeSwitch :: [(Annotated Lower Exp, Annotated Lower Exp)] -> Praxis [(Annotated Lower Exp, Annotated Lower Exp)]
  consumeSwitch [] = return []
  consumeSwitch ((cond, body) : alts)
    | used body || any (\(c, b) -> used c || used b) alts = do
        cond' <- retain cond
        body' <- consume body
        alts' <- if any (\(c, b) -> used c || used b) alts
          then consumeSwitch alts
          else return [ (c, dropAfter x xTy b) | (c, b) <- alts ]
        return ((cond', body') : alts')
    | otherwise = do
        -- The condition consumes the variable. Nothing after it uses the variable, so nothing to do there (in particular,
        -- the fall through after the last condition fails is unreachable).
        cond' <- consume cond
        return ((cond', body) : alts)

  -- The last child (in evaluation order) to use the variable consumes it, earlier ones retain it.
  consumeLast :: Exp Lower -> Praxis (Exp Lower)
  consumeLast exp = evalStateT (recurseTerm step exp) 0 where
    flags = getConst (recurseTerm flag exp)
    flag :: forall a. IsTerm a => Annotated Lower a -> Const [Bool] (Annotated Lower a)
    flag child = case typeof (view value child) of
      ExpT -> Const [used child]
      _    -> Const []
    lastUse = length flags - 1 - length (takeWhile not (reverse flags))
    step :: forall a. IsTerm a => Annotated Lower a -> StateT Int Praxis (Annotated Lower a)
    step child = case typeof (view value child) of
      ExpT -> do
        i <- get
        put (i + 1)
        lift $ if i == lastUse then consume child else if used child then retain child else return child
      _ -> return child

  -- Precondition: the variable is owned. Postcondition: the variable is still owned on every path (i.e. every use is a copy).
  retain :: Annotated Lower Exp -> Praxis (Annotated Lower Exp)
  retain e@((src, ty) :< exp)
    | not (used e) = return e
    | otherwise = ((src, ty) :<) <$> case exp of

        Var _
          | copyable  -> return (view value (copyOf x xTy))
          | otherwise -> error ("linearize: affine variable " ++ nameString x ++ " is used more than once")

        -- The closure takes a copy of the captured variable
        Closure caps code | x `elem` map fst caps -> do
          x' <- freshVar (mkName (nameString x ++ "_copy"))
          let caps' = [ (if name == x then x' else name, t) | (name, t) <- caps ]
          return (Let (phantom (Bind ((Phantom, xTy) :< PatVar x') (copyOf x xTy))) ((src, ty) :< Closure caps' code))

        _ -> retainAll exp

  retainAll :: forall a. IsTerm a => a Lower -> Praxis (a Lower)
  retainAll = recurseTerm child where
    child :: forall b. IsTerm b => Annotated Lower b -> Praxis (Annotated Lower b)
    child term = case typeof (view value term) of
      ExpT -> retain term
      _    -> value retainAll term


-- * Helpers

-- | @e defer drop x@
dropAfter :: Name -> Type' -> Annotated Lower Exp -> Annotated Lower Exp
dropAfter x xTy e@((src, ty) :< _) = (src, ty) :< Defer e (inbuiltApply InbuiltDrop (phantom TypeUnit) x xTy)

-- | @copy x@
copyOf :: Name -> Type' -> Annotated Lower Exp
copyOf x xTy = inbuiltApply InbuiltCopy xTy x xTy

-- | Apply a polymorphic inbuilt (specialized to the type of the variable) to a variable.
inbuiltApply :: Inbuilt -> Type' -> Name -> Type' -> Annotated Lower Exp
inbuiltApply inbuilt retTy x xTy = (Phantom, retTy) :< Apply fn ((Phantom, xTy) :< Var x) where
  fnTy = phantom (TypeFn xTy retTy)
  spec = [ (phantom (TypePatVar Plain (mkName "a")), castType xTy) ]
  fn = (Phantom, fnTy) :< Specialize ((Phantom, fnTy) :< Inbuilt inbuilt) spec

-- | Types carry no annotation in either stage, so they can be freely cast.
castType :: Annotated TypeCheck Type -> Annotated Lower Type
castType = cast where
  cast :: forall a. IsTerm a => Annotated TypeCheck a -> Annotated Lower a
  cast ((src, _) :< term) = case termT :: TermT a of
    TypeT -> (src, ()) :< runIdentity (recurseTerm (Identity . cast) term)

-- | The variables bound by a pattern, with their types.
patVars :: Annotated Lower Pat -> [(Name, Type')]
patVars ((_, ty) :< pat) = case pat of
  PatAt name inner -> (name, ty) : patVars inner
  PatData _ inner  -> patVars inner
  PatPair l r      -> patVars l ++ patVars r
  PatVar name      -> [(name, ty)]
  _                -> []
