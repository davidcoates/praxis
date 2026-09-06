{-# LANGUAGE TypeFamilies #-}

-- | Closure conversion.
--
-- Every function body is lifted to a top-level declaration, so that after this pass:
--
--   * 'Lambda' and 'Cases' appear only as the immediate body of a top-level declaration.
--   * 'Closure' only wraps a 'Var' referring to a top-level function, and denotes the
--     (uncurried) partial application of that function to the tuple of captured values.
--     A function with captures @c1 .. cn@ and original type @a -> b@ is lifted with type
--     @((c1, (.., cn)), a) -> b@.
--   * 'Where' does not appear; value bindings become 'Let's.
--   * Calls to where-bound functions are direct calls to the lifted function, with the
--     captured values passed explicitly as the first component of the argument.
module Lower.ClosureConvert
  ( run
  , runExp
  ) where

import           Common
import           Introspect
import           Praxis
import           Stage
import           Term

import           Control.Monad       (foldM)
import           Control.Monad.State (StateT, modify, runStateT)
import           Control.Monad.Trans (lift)
import           Data.Map.Strict     (Map)
import qualified Data.Map.Strict     as Map
import           Data.Set            (Set)
import qualified Data.Set            as Set


type Type' = Annotated TypeCheck Type

type Captures = [(Name, Type')]

-- | A function which has been lifted to the top level.
data Lifted = Lifted
  { liftedName     :: Name
  -- ^ The top-level name of the lifted function.
  , liftedType     :: Type'
  -- ^ The type of the lifted function (taking the captures as the first argument component, if there are any).
  , liftedCaptures :: Captures
  }

data Env = Env
  { locals    :: Set Name
  -- ^ Variables bound within the current top-level declaration (only these can be captured).
  , lifted    :: Map Name Lifted
  -- ^ Where-bound functions in scope, by their original name.
  , enclosing :: Name
  -- ^ The enclosing top-level declaration, used to name lifted anonymous functions.
  }

-- | Accumulates lifted top-level declarations.
type ConvertM = StateT [Annotated Lower Decl] Praxis

emit :: Annotated Lower Decl -> ConvertM ()
emit decl = modify (++ [decl])


-- * Entry points

run :: Annotated Lower Program -> Praxis (Annotated Lower Program)
run (_ :< Program decls) = do
  decls' <- concat <$> mapM convertTopDecl decls
  let result = phantom (Program decls')
  display Lower "closure converted program" result `ifFlag` debug
  return result

-- | Convert a standalone expression against an already converted program.
-- Any lifted declarations are appended to the program.
runExp :: Annotated Lower Program -> Annotated Lower Exp -> Praxis (Annotated Lower Program, Annotated Lower Exp)
runExp (_ :< Program decls) exp = do
  (exp', liftedDecls) <- runStateT (convertExp (emptyEnv (mkName "it")) exp) []
  let result = phantom (Program (decls ++ liftedDecls))
  display Lower "closure converted program" result `ifFlag` debug
  display Lower "closure converted exp" exp' `ifFlag` debug
  return (result, exp')

emptyEnv :: Name -> Env
emptyEnv name = Env { locals = Set.empty, lifted = Map.empty, enclosing = name }


-- * Declarations

-- | Convert a top-level declaration. Lifted declarations are placed immediately before it.
convertTopDecl :: Annotated Lower Decl -> Praxis [Annotated Lower Decl]
convertTopDecl decl = do
  (decl', liftedDecls) <- runStateT (convertDecl decl) []
  return (liftedDecls ++ [decl'])

convertDecl :: Annotated Lower Decl -> ConvertM (Annotated Lower Decl)
convertDecl (a :< decl) = (a :<) <$> case decl of
  DeclTerm dt -> DeclTerm <$> convertDeclTerm dt
  DeclRec ds  -> DeclRec <$> mapM convertDeclRec ds
  _           -> return decl

convertDeclRec :: Annotated Lower DeclRec -> ConvertM (Annotated Lower DeclRec)
convertDeclRec (a :< dr) = (a :<) <$> case dr of
  DeclRecTerm dt -> DeclRecTerm <$> convertDeclTerm dt
  _              -> return dr

convertDeclTerm :: Annotated Lower DeclTerm -> ConvertM (Annotated Lower DeclTerm)
convertDeclTerm (a :< DeclTermVar name qTy body) = do
  let env = emptyEnv name
  body' <- case view value body of
    -- A top-level function. The closure wrapper is redundant, since there is nothing to capture.
    Closure [] fn -> convertFunction env fn
    Closure _ _   -> error "top-level closure with captures"
    _             -> convertExp env body
  return (a :< DeclTermVar name qTy body')
convertDeclTerm dt = return dt


-- * Expressions

convertExp :: Env -> Annotated Lower Exp -> ConvertM (Annotated Lower Exp)
convertExp env ((src, ty) :< exp) = case exp of

  Var name | Just l <- Map.lookup name (lifted env) -> return (reference src ty l)

  Apply f arg -> do
    arg' <- convertExp env arg
    case view value f of
      Var name | Just l <- Map.lookup name (lifted env) -> return (call src ty l arg')
      _ -> do
        f' <- convertExp env f
        return $ case view value f' of
          -- An immediately applied closure can be called directly.
          Closure caps (_ :< Var code) | not (null caps) ->
            call src ty (Lifted { liftedName = code, liftedType = view annotation (closureCode f'), liftedCaptures = uncaptures caps }) arg'
          _ -> (src, ty) :< Apply f' arg'

  -- An anonymous function
  Closure _ fn -> do
    fn' <- convertFunction env fn
    let caps = captures env fn'
    code <- lift $ freshVar (mkName (nameString (enclosing env) ++ "_lambda"))
    l <- liftFunction code ty caps fn'
    return (reference src ty l)

  Lambda _ _ -> error "unexpected lambda outside of closure"

  Cases _ -> error "unexpected cases outside of closure"

  Where body decls -> do
    (env', binds) <- foldM whereDecl (env, []) decls
    body' <- convertExp env' body
    let mkLet (name, rhs) body = (src, view annotation body) :< Let (phantom (Bind ((Phantom, view annotation rhs) :< PatVar name) rhs)) body
    return (foldr mkLet body' binds)

  Let (b :< Bind pat rhs) body -> do
    rhs'  <- convertExp env rhs
    body' <- convertExp (bind (patNames pat) env) body
    return ((src, ty) :< Let (b :< Bind pat rhs') body')

  Case scrut alts -> do
    scrut' <- convertExp env scrut
    alts'  <- mapM (convertAlt env) alts
    return ((src, ty) :< Case scrut' alts')

  _ -> ((src, ty) :<) <$> recurseTerm convertChild exp

  where
    convertChild :: forall a. IsTerm a => Annotated Lower a -> ConvertM (Annotated Lower a)
    convertChild child = case typeof (view value child) of
      ExpT -> convertExp env child
      _    -> return child

    -- Process one declaration of a where block, either lifting it (if it is a function) or turning it in to a let binding.
    whereDecl :: (Env, [(Name, Annotated Lower Exp)]) -> Annotated Lower DeclTerm -> ConvertM (Env, [(Name, Annotated Lower Exp)])
    whereDecl (env, binds) (_ :< DeclTermVar name _ rhs) = case view value rhs of
      Closure _ fn -> do
        fn' <- convertFunction env fn
        let caps = captures env fn'
        code <- lift $ freshVar name
        l <- liftFunction code (view annotation rhs) caps fn'
        return (env { lifted = Map.insert name l (lifted env) }, binds)
      _ -> do
        rhs' <- convertExp env rhs
        return (bind (Set.singleton name) env, binds ++ [(name, rhs')])
    whereDecl acc _ = return acc

convertAlt :: Env -> (Annotated Lower Pat, Annotated Lower Exp) -> ConvertM (Annotated Lower Pat, Annotated Lower Exp)
convertAlt env (pat, exp) = (pat,) <$> convertExp (bind (patNames pat) env) exp

-- | Convert the body of a function ('Lambda' or 'Cases'), leaving the function itself in place.
convertFunction :: Env -> Annotated Lower Exp -> ConvertM (Annotated Lower Exp)
convertFunction env ((src, ty) :< fn) = ((src, ty) :<) <$> case fn of
  Lambda pat body -> Lambda pat <$> convertExp (bind (patNames pat) env) body
  Cases alts      -> Cases <$> mapM (convertAlt env) alts
  _               -> error "expected a function"

bind :: Set Name -> Env -> Env
bind names env = env { locals = locals env <> names }


-- * Lifting

-- | Emit a top-level declaration for a function with the given captures, returning how to refer to it.
liftFunction :: Name -> Type' -> Captures -> Annotated Lower Exp -> ConvertM Lifted
liftFunction code fnTy caps fn = do
  (liftedTy, body) <- case caps of
    [] -> return (fnTy, fn)
    _  -> do
      let
        (argTy, retTy) = case view value fnTy of
          TypeFn argTy retTy -> (argTy, retTy)
          _                  -> error "expected a function type"
        capsTy = tupleType (map snd caps)
        paramTy = phantom (TypePair capsTy argTy)
        liftedTy = phantom (TypeFn paramTy retTy)
      body <- case view value fn of
        Lambda pat body -> return (Lambda ((Phantom, paramTy) :< PatPair (tuplePat caps) pat) body)
        Cases alts -> do
          arg <- lift $ freshVar (mkName "arg")
          let scrut = (Phantom, argTy) :< Var arg
          return (Lambda ((Phantom, paramTy) :< PatPair (tuplePat caps) ((Phantom, argTy) :< PatVar arg)) ((Phantom, retTy) :< Case scrut alts))
        _ -> error "expected a function"
      return (liftedTy, (Phantom, liftedTy) :< body)
  emit $ phantom (DeclTerm (phantom (DeclTermVar code (Just (phantom (Mono (castType liftedTy)))) body)))
  return Lifted { liftedName = code, liftedType = liftedTy, liftedCaptures = caps }

-- | A reference to a lifted function as a value.
reference :: Source -> Type' -> Lifted -> Annotated Lower Exp
reference src ty l = case liftedCaptures l of
  []   -> (src, ty) :< Var (liftedName l)
  caps -> (src, ty) :< Closure [ (name, phantom (Mono (castType t))) | (name, t) <- caps ] ((Phantom, liftedType l) :< Var (liftedName l))

-- | A direct call to a lifted function.
call :: Source -> Type' -> Lifted -> Annotated Lower Exp -> Annotated Lower Exp
call src ty l arg = (src, ty) :< Apply code arg' where
  code = (Phantom, liftedType l) :< Var (liftedName l)
  arg' = case liftedCaptures l of
    []   -> arg
    caps -> (Phantom, phantom (TypePair (tupleType (map snd caps)) (view annotation arg))) :< Pair (tupleExp caps) arg

closureCode :: Annotated Lower Exp -> Annotated Lower Exp
closureCode (_ :< Closure _ code) = code
closureCode _                     = error "expected a closure"

uncaptures :: [(Name, Annotated Lower QType)] -> Captures
uncaptures caps = [ (name, uncastType t) | (name, _ :< Mono t) <- caps ]


-- * Capture tuples

-- | Captured values are packed in to a right-nested tuple.
tupleType :: [Type'] -> Type'
tupleType []       = phantom TypeUnit
tupleType [t]      = t
tupleType (t : ts) = phantom (TypePair t (tupleType ts))

tuplePat :: Captures -> Annotated Lower Pat
tuplePat []             = (Phantom, phantom TypeUnit) :< PatUnit
tuplePat [(n, t)]       = (Phantom, t) :< PatVar n
tuplePat ((n, t) : cs)  = (Phantom, tupleType (t : map snd cs)) :< PatPair ((Phantom, t) :< PatVar n) (tuplePat cs)

tupleExp :: Captures -> Annotated Lower Exp
tupleExp []             = (Phantom, phantom TypeUnit) :< Unit
tupleExp [(n, t)]       = (Phantom, t) :< Var n
tupleExp ((n, t) : cs)  = (Phantom, tupleType (t : map snd cs)) :< Pair ((Phantom, t) :< Var n) (tupleExp cs)


-- * Free variables

-- | The local variables captured by a function, with their types.
captures :: Env -> Annotated Lower Exp -> Captures
captures env fn = Map.toAscList (Map.filterWithKey (\name _ -> name `Set.member` locals env) (freeVars fn))

-- | The free variables of an expression, with their types.
freeVars :: Annotated Lower Exp -> Map Name Type'
freeVars ((_, ty) :< exp) = case exp of
  Var name             -> Map.singleton name ty
  Closure caps code    -> Map.fromList (uncaptures caps) <> freeVars code
  Lambda pat body      -> freeVars body `without` patNames pat
  Cases alts           -> foldMap alt alts
  Case scrut alts      -> freeVars scrut <> foldMap alt alts
  Let (_ :< Bind pat rhs) body -> freeVars rhs <> (freeVars body `without` patNames pat)
  Where body decls     -> foldr whereDecl (freeVars body) decls
  _                    -> getConst (recurseTerm child exp)
  where
    alt (pat, body) = freeVars body `without` patNames pat
    whereDecl (_ :< DeclTermVar name _ rhs) rest = freeVars rhs <> Map.delete name rest
    whereDecl _ rest = rest
    child :: forall a. IsTerm a => Annotated Lower a -> Const (Map Name Type') (Annotated Lower a)
    child term = case typeof (view value term) of
      ExpT -> Const (freeVars term)
      _    -> Const Map.empty

without :: Map Name a -> Set Name -> Map Name a
without = Map.withoutKeys

patNames :: Annotated Lower Pat -> Set Name
patNames (_ :< pat) = case pat of
  PatAt name inner -> Set.insert name (patNames inner)
  PatData _ inner  -> patNames inner
  PatPair l r      -> patNames l <> patNames r
  PatVar name      -> Set.singleton name
  _                -> Set.empty


-- * Type casting

-- Types carry no annotation in either stage, so they can be freely cast between the two.

castType :: Annotated TypeCheck Type -> Annotated Lower Type
castType = cast where
  cast :: forall a. IsTerm a => Annotated TypeCheck a -> Annotated Lower a
  cast ((src, _) :< term) = case termT :: TermT a of
    TypeT -> (src, ()) :< runIdentity (recurseTerm (Identity . cast) term)

uncastType :: Annotated Lower Type -> Annotated TypeCheck Type
uncastType = cast where
  cast :: forall a. IsTerm a => Annotated Lower a -> Annotated TypeCheck a
  cast ((src, _) :< term) = case termT :: TermT a of
    TypeT -> (src, ()) :< runIdentity (recurseTerm (Identity . cast) term)
