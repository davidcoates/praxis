module Eval
  ( run
  , runMain

  , Evaluation(..)
  ) where

import qualified Check.State       as Check
import           Common
import qualified Data.Map.Strict   as Map
import           Eval.State
import           Eval.Value        (Value, integerToValue, valueToInteger)
import qualified Eval.Value        as Value
import           Introspect
import           Praxis
import           Stage
import qualified Term
import           Term              hiding (Annotated (..))


import           Control.Monad.Fix (mfix)
import           Data.Array.IO
import           Data.List         (partition)
import           Data.Maybe        (mapMaybe)


type Annotated a = Term.Annotated Monomorphize a

type family Evaluation a where
  Evaluation Exp = Value
  Evaluation _   = ()

run :: IsTerm a => Annotated a -> Praxis (Evaluation a)
run term = eval term

runMain :: Praxis ()
runMain = do
  entry <- (checkState . Check.typeState . Check.varRename . Check.renames) `uses` Map.lookup (mkName "main")
  case entry of
    Nothing -> throw Evaluate ("missing main function" :: String)
    Just rename -> do
      entry <- (checkState . Check.typeState . Check.varEnv) `uses` Map.lookup rename
      case entry of
        Just (_, qTy)
          | (_ :< Mono (_ :< TypeFn (_ :< TypeUnit) (_ :< TypeUnit))) <- qTy
            -> do
              Just (Value.Fn f) <- (evalState . valueEnv) `uses` Map.lookup rename
              f Value.Unit
              return ()
          | otherwise
            -> throwAt Evaluate (view source qTy) $ "main function has bad type " <> pretty qTy <> ", expected () -> ()"

eval :: IsTerm a => Annotated a -> Praxis (Evaluation a)
eval term = ($ term) $ case typeof (view value term) of
  ProgramT -> evalProgram
  ExpT     -> evalExp

evalProgram :: Annotated Program -> Praxis ()
evalProgram (_ :< Program decls) = traverse evalDecl decls >> return ()

-- | A helper for decls, irrefutably matching the [b] argument
irrefMapM :: Monad m => ((a, b) -> m c) -> [a] -> [b] -> m [c]
irrefMapM f as bs = case as of
  []     -> return []
  (a:as) -> case bs of
    ~(b:bs) -> do
      c <- f (a, b)
      cs <- irrefMapM f as bs
      return (c : cs)

evalDecl :: Annotated Decl -> Praxis ()
evalDecl (_ :< decl) = case decl of

  DeclRec decls -> do
    let
      declTerms = mapMaybe (\(_ :< decl) -> case decl of { DeclRecTerm declTerm -> Just declTerm; _ -> Nothing }) decls
      (names, exps) = unzip [ (name, exp) | (_ :< DeclTermVar name _ exp) <- declTerms ]
    -- To support mutual recursion, each function needs to see the evaluation of all other functions (including itself).
    -- Leverage mfix to find the fixpoint.
    mfix $ \values -> do
      -- Evaluate each of the functions in turn, with all of the evaluations in the environment
      -- Note: The use of irrefMapM here is essential to avoid divergence of mfix.
      irrefMapM (\(name, value) -> (evalState . valueEnv) %= Map.insert name value) names values
      traverse evalExp exps
    return ()

  DeclTerm decl -> evalDeclTerm decl

  DeclType _ -> return ()


evalDeclTerm :: Annotated DeclTerm -> Praxis ()
evalDeclTerm (_ :< decl) = case decl of

  DeclTermVar name _ exp -> do
    value <- evalExp exp
    (evalState . valueEnv) %= Map.insert name value


lookupValue :: Source -> Name -> Praxis Value
lookupValue src name = do
  entry <- (evalState . valueEnv) `uses` Map.lookup name
  case entry of
     Just val -> return val
     Nothing  -> throwAt Evaluate src ("unknown variable " <> pretty name)

evalExp :: Annotated Exp -> Praxis Value
evalExp ((src, ty) :< exp) = case exp of

  Apply f x -> do
    Value.Fn f <- evalExp f
    x <- evalExp x
    f x

  Capture captures exp -> do
    let names = map fst captures
    display Evaluate "captures" (show (map fst captures)) `ifFlag` debug
    display Evaluate "exp" exp `ifFlag` debug
    values <- traverse (lookupValue src) names
    Value.Fn fn <- evalExp exp
    return $ Value.Fn $ \val -> save (evalState . valueEnv) $ do
      mapM_ (\(n, v) -> (evalState . valueEnv) %= Map.insert n v) (zip names values)
      fn val

  Case exp alts -> do
    val <- evalExp exp
    evalCase src val alts

  Cases alts -> return $ Value.Fn $ \val -> evalCase src val alts

  Con name -> do
    case ty of
      (_ :< TypeFn _ _) -> return $ Value.Fn (\val -> return $ Value.Data name val)
      _                 -> return $ Value.Enum name

  Defer exp1 exp2 -> do
    val <- evalExp exp1
    evalExp exp2
    return val

  If condExp thenExp elseExp -> do
    Value.Bool cond <- evalExp condExp
    if cond then evalExp thenExp else evalExp elseExp

  Inbuilt inbuilt -> evalInbuilt inbuilt []

  Specialize (_ :< Inbuilt inbuilt) specialization -> evalInbuilt inbuilt specialization

  Lambda pat exp -> return $ Value.Fn $ \val -> forceMatch src val pat >> evalExp exp

  Let bind exp -> save (evalState . valueEnv) $ do
    evalBind bind
    evalExp exp

  Lit lit -> pure $ case lit of
    Bool    val -> Value.Bool val
    Char    val -> Value.Char val
    Integer val -> let (_ :< TypeCon n) = ty in integerToValue n val
    String  val -> Value.String val

  Read _ exp -> evalExp exp

  Pair exp1 exp2 -> Value.Pair <$> evalExp exp1 <*> evalExp exp2

  Seq exp1 exp2 -> do
    evalExp exp1
    val <- evalExp exp2
    return val

  Sig exp _ -> evalExp exp


  Switch alts -> evalSwitch src alts

  Term.Unit -> return Value.Unit

  Var var -> lookupValue src var

  Where exp decls -> save (evalState . valueEnv) $ do
    traverse evalDeclTerm decls
    evalExp exp


evalInbuilt :: Inbuilt -> Specialization Monomorphize -> Praxis Value
evalInbuilt inbuilt specialization = return $ case inbuilt of
  Add      -> liftIII (+)
  Subtract -> liftIII (-)
  Multiply -> liftIII (*)
  Negate   -> liftI $ \(con, decon) -> Value.Fn (\x -> return (con (negate (decon x))))
  GetInt   -> liftI $ \(con, _)     -> Value.Fn (\Value.Unit -> liftIOUnsafe (con <$> readLn))
  PutInt   -> liftI $ \(_, decon)   -> Value.Fn (\i -> liftIOUnsafe (print (decon i) >> pure Value.Unit))
  Eq       -> liftIIB (==)
  Neq      -> liftIIB (/=)
  Lt       -> liftIIB (<)
  Gt       -> liftIIB (>)
  Lte      -> liftIIB (<=)
  Gte      -> liftIIB (>=)
  GetStr   -> Value.Fn (\Value.Unit -> Value.String <$> liftIOUnsafe getContents)
  PutStr   -> Value.Fn (\(Value.String s) -> liftIOUnsafe (putStr s) >> pure Value.Unit)
  PutStrLn -> Value.Fn (\(Value.String s) -> liftIOUnsafe (putStrLn s) >> pure Value.Unit)
  Compose  -> Value.Fn (\(Value.Pair (Value.Fn f) (Value.Fn g)) -> pure (Value.Fn (\x -> g x >>= f)))
  Print    -> Value.Fn (\x -> liftIOUnsafe (print x) >> pure Value.Unit)
  NewArray -> Value.Fn (\(Value.Pair (Value.USize n) v) -> Value.newArray n v)
  AtArray  -> Value.Fn (\(Value.Pair (Value.Array a) (Value.USize i)) -> Value.readArray a i)
  LenArray -> Value.Fn (\(Value.Array a) -> Value.USize <$> Value.lenArray a)
  SetArray -> Value.Fn (\(Value.Pair (Value.Array a) (Value.Pair (Value.USize i) e)) -> Value.writeArray a i e >> pure (Value.Array a))
  Not      -> Value.Fn (\(Value.Bool a) -> pure (Value.Bool (not a)))
  Or       -> Value.Fn (\(Value.Pair (Value.Bool a) (Value.Bool b)) -> pure (Value.Bool (a || b)))
  And      -> Value.Fn (\(Value.Pair (Value.Bool a) (Value.Bool b)) -> pure (Value.Bool (a && b)))
  where
    (con, decon) = case specialization of
      [(_, _ :< TypeCon ty)] -> (integerToValue ty, valueToInteger)
      _                      -> (error "evalInbuilt: missing spec", error "evalInbuilt: missing spec")
    liftI f = f (con, decon)
    liftIII f = Value.Fn (\(Value.Pair x y) -> return (con (f (decon x) (decon y))))
    liftIIB f = Value.Fn (\(Value.Pair x y) -> return (Value.Bool (f (decon x) (decon y))))

evalSwitch :: Source -> [(Annotated Exp, Annotated Exp)] -> Praxis Value
evalSwitch src [] = throwAt Evaluate src ("inexhaustive switch" :: String)
evalSwitch src ((condExp,bodyExp):alts) = do
  cond <- evalExp condExp
  case cond of
    Value.Bool True  -> evalExp bodyExp
    Value.Bool False -> evalSwitch src alts

evalCase :: Source -> Value -> [(Annotated Pat, Annotated Exp)] -> Praxis Value
evalCase src val [] = throwAt Evaluate src ("no matching pattern for value " <> pretty (show val))
evalCase src val ((pat,exp):alts) = case tryMatch val pat of
  Just doMatch -> save (evalState . valueEnv) $ do
    doMatch
    evalExp exp
  Nothing ->
    evalCase src val alts

forceMatch :: Source -> Value -> Annotated Pat -> Praxis ()
forceMatch src val pat = case tryMatch val pat of
  Just doMatch -> doMatch
  Nothing -> throwAt Evaluate src ("no matching pattern for value " <> pretty (show val))

evalBind :: Annotated Bind -> Praxis ()
evalBind ((src, _) :< Bind pat exp) = do
  exp <- evalExp exp
  forceMatch src exp pat

tryMatch :: Value -> Annotated Pat -> Maybe (Praxis ())
tryMatch val ((_, t) :< pat) = case pat of

  PatAt name pat
    -> (\doMatch -> do { evalState . valueEnv %= Map.insert name val; doMatch }) <$> tryMatch val pat

  PatData name pat | Value.Data name' val <- val
    -> if name == name' then tryMatch val pat else Nothing

  PatEnum name | Value.Enum name' <- val
    -> if name == name' then Just (return ()) else Nothing

  PatHole
    -> Just (return ())

  PatLit pat -> if match then Just (return ()) else Nothing where
    match = case (pat, val) of
      (Bool x, Value.Bool y) -> x == y
      (Char x, Value.Char y) -> x == y
      (Integer x, y)         -> x == valueToInteger y
      _                      -> False

  PatPair pat1 pat2 | Value.Pair val1 val2 <- val
    -> liftA2 (>>) (tryMatch val1 pat1) (tryMatch val2 pat2)

  PatUnit
    -> Just (return ())

  PatVar name
    -> Just $ evalState . valueEnv %= Map.insert name val

  _
    -> Nothing
