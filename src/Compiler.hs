{-# LANGUAGE TemplateHaskell, RankNTypes #-}

module Compiler
  ( Compiler
  , CompilerState
  , initialState
  , throwError
  , internalError -- Prefer this over Prelude.error
  , Stage(..)

  , get
  , getWith
  , set
  , over

  , save
  , independently

  , run
  , runWith
  , lift
  , liftIO -- ^Lifts an IO computation to the Compiler monad

  -- |Flag lenses
  , debug

  -- |Compiler lenses (TODO order these)
  , flags
  , stage
  , imports
  , filename
  , src
  , tokens
  , sugaredAST
  , desugaredAST
  , tEnv
  , vEnv
  , qtEnv
  , typedAST
  , inClosure

  , freshUniT
  , freshUniP
  , freshUniE
  , freshVar

  , ungeneralise

  , debugPrint
  , debugPutStrLn
  )
  where

import AST (Lit)
import qualified Check.AST as Check
import Common
import Env (QTEnv, TEnv, VEnv)
import Error (Error)
import qualified Parse.Parse.AST as Parse
import qualified Parse.Desugar.AST as Desugar
import qualified Parse.Tokenise.Token as Tokenise
import Record (Record)
import Source
import Type

import Control.Applicative (liftA2)
import qualified Control.Lens (set, over)
import Control.Lens (Lens', view, makeLenses)
import Control.Monad (void)
import qualified Control.Monad (when, unless)
import Control.Monad.Except (ExceptT, runExceptT)
import qualified Control.Monad.Except (throwError)
import Control.Monad.State (StateT, runStateT, lift, put, gets, modify)
import qualified Control.Monad.State as State (get)
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import System.IO.Unsafe (unsafePerformIO)

data Stage = Tokenise
           | Parse
           | Desugar
           | Check
           | Generate
           | Solve
           | Evaluate
-- TODO CodeGenerate

instance Show Stage where
  show Tokenise           = "Tokeniser"
  show Parse              = "Parser"
  show Desugar            = "Desugarer"
  show Check              = "Inference"
  show Generate           = "Inference (Constraint Generator)"
  show Solve              = "Inference (Contraint Solver)"
  show Evaluate           = "Evaluate"


type Token = Tokenise.Annotated Tokenise.Token

data Flags = Flags { _debug :: Bool, _static :: Bool } -- static is NOT exported
  deriving (Show)

data CompilerState = CompilerState
  { _flags        :: Flags
  , _stage        :: Stage               -- ^Current stage of compilation
  , _freshUnis    :: [String]            -- ^Infinite list of distinct dummy names to use for unification types
  , _freshVars    :: [String]            -- ^Infinite list of distinct dummy names to use for phantom variables
  , _imports      :: [FilePath]          -- ^Loaded modules
  , _filename     :: FilePath            -- ^File path (for error messages)
  , _src          :: String              -- ^Source to compile
  , _tokens       :: [Token]             -- ^List of tokens produced by tokeniser
  , _sugaredAST   :: Parse.AST           -- ^AST after parsing of tokens
  , _desugaredAST :: Desugar.AST         -- ^AST after desugaring
  , _typedAST     :: Check.AST           -- ^AST after type inference
  , _qtEnv        :: QTEnv               -- ^Type environment of top-level functions
  , _tEnv         :: TEnv                -- ^Type environment of local functions
  , _kEnv         :: ()                  -- TODO (Kind environment)
  , _vEnv         :: VEnv                -- ^Value environment for interpreter

  , _inClosure    :: Bool                -- ^Checker (Generator) internal
  {-
  , _fname    :: Maybe FilePath            -- ^File path
  , _imports  :: [FilePath]                -- ^Loaded modules
  , _src      :: Maybe L.Text              -- ^File source
  , _ast      :: Maybe Syn.Module          -- ^Frontend AST
  , _tenv     :: Env.Env                   -- ^Typing environment
  , _kenv     :: Map.Map Name Kind         -- ^Kind environment
  , _cenv     :: ClassEnv.ClassEnv         -- ^Typeclass environment
  , _cast     :: Maybe Core.Module         -- ^Core AST
  , _flags    :: Flags.Flags               -- ^Compiler flags
  , _venv     :: CoreEval.ValEnv Core.Expr -- ^Core interpreter environment
  , _denv     :: DataEnv.DataEnv           -- ^Entity dictionary
  , _clenv    :: ClassEnv.ClassHier        -- ^Typeclass hierarchy
  -}

  } deriving (Show)

type Compiler a = ExceptT Error (StateT CompilerState IO) a

defaultFlags :: Flags
defaultFlags = Flags { _debug = True, _static = False }

get :: Lens' CompilerState a -> Compiler a
get = lift . gets . view

getWith :: Lens' CompilerState a -> (a -> b) -> Compiler b
getWith l f = do
  x <- get l
  return (f x)

set :: Lens' CompilerState a -> a -> Compiler ()
set l x = lift . modify $ Control.Lens.set l x

over :: Lens' CompilerState a -> (a -> a) -> Compiler ()
over l f = do
  x <- get l
  set l (f x)

throwError :: Error -> Compiler a
throwError = Control.Monad.Except.throwError

-- filenameDisplay :: Compiler e String
-- filenameDisplay = fromMaybe "<interactive>" <$> getRaw filename

initialState :: CompilerState
initialState  = CompilerState
  { _flags        = defaultFlags
  , _stage        = unset "stage"
  , _freshUnis    = map ('~':) (fresh ['a'..'z'])
  , _freshVars    = map ('_':) (fresh ['a'..'z'])
  , _imports      = unset "imports"
  , _filename     = "<stdin>"
  , _src          = unset "src"
  , _tokens       = unset "tokens"
  , _sugaredAST   = unset "sugaredAST"
  , _desugaredAST = unset "desugaredAST"
  , _qtEnv        = unset "qtEnv"
  , _tEnv         = unset "tenv"
  , _kEnv         = unset "kenv"
  , _typedAST     = unset "typedAST"
  , _vEnv         = unset "vEnv"
  , _inClosure    = unset "inClosure"
  }
  where unset s = internalError ("unset " ++ s)


fresh :: String -> [String]
fresh alpha = concatMap perm [1..]
  where perm :: Int -> [String]
        perm 1 = map (:[]) alpha
        perm n = do { x <- alpha; y <- perm (n-1); return (x:y) }


internalError :: String -> a
internalError s = error ("<<<INTERNAL ERROR>>> " ++ s)

makeLenses ''Flags
makeLenses ''CompilerState

save :: Lens' CompilerState a -> Compiler b -> Compiler b
save l c = do
  x <- get l
  r <- c
  set l x
  return r

runStatic :: Compiler a -> a
runStatic c = let (Right x, _) = unsafePerformIO (run c') in x
  where c' = set (flags . static) True >> set (flags . debug) False >> c
    -- TODO instead of hiding debugging output, perhaps debug* should check static flag

-- | Performs a computation independent from the current state
independently :: Compiler a -> Compiler a
independently c = do
  saved <- lift State.get
  s <- get (flags . static)
  lift $ put initialState
  set (flags . static) s
  r <- c
  lift $ put saved
  return r

assert :: Lens' CompilerState a -> (a -> Bool) -> String -> Compiler b -> Compiler b
assert l p s c = do
  x <- get l
  if p x then c else internalError s

liftIO :: IO a -> Compiler a
liftIO io = assert (flags . static) (== False) "TODO not static" (lift (lift io))

run :: Compiler a -> IO (Either Error a, CompilerState)
run c = runWith c initialState

runWith :: Compiler a -> CompilerState -> IO (Either Error a, CompilerState)
runWith = runStateT . runExceptT

when :: Lens' CompilerState Bool -> Compiler a -> Compiler ()
when l c = do
  b <- get l
  Control.Monad.when b (void c)

unless :: Lens' CompilerState Bool -> Compiler a -> Compiler ()
unless l c = do
  b <- get l
  Control.Monad.unless b (void c)

-- TODO this possibly shouldnt be here
debugPrint :: Show a => a -> Compiler ()
debugPrint = debugPutStrLn . show

debugPutStrLn :: String -> Compiler ()
debugPutStrLn x = when (flags . debug) $ unless (flags . static) $ do
    s <- get stage
    liftIO $ putStrLn ("Output from stage: " ++ show s)
    liftIO $ putStrLn x

-- TODO: Stuff below this probably shouldn't be here...
freshUniT :: Compiler Type
freshUniT = liftA2 (:#) freshUniP freshUniE

freshUniP :: Compiler Pure
freshUniP = do
  (x:xs) <- get freshUnis
  set freshUnis xs
  return (TyUni x)

freshUniE :: Compiler Effects
freshUniE = do
  (x:xs) <- get freshUnis
  set freshUnis xs
  return (singleton (EfUni x))

freshVar :: Compiler Name
freshVar = do
  (x:xs) <- get freshVars
  set freshVars xs
  return x


-- TODO: Allow quantified effects
ungeneralise :: QPure -> Compiler ([Constraint], Pure)
ungeneralise (Forall cs as t) = do
  bs <- sequence (replicate (length as) freshUniP)
  let ft = (`lookup` zip as bs)
  let fe = const Nothing
  let subsP = subsPure ft fe
  return (map (\c -> case c of Class s t -> Class s (subsP t)) cs, subsP t)


