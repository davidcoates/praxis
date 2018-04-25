{-# LANGUAGE TemplateHaskell, RankNTypes #-}

module Compiler
  ( Compiler
  , CompilerState
  , initialState
  , throwError
  , Stage(..)

  , get
  , set
  , run
  , runWith
  , lift
  , liftIO -- ^ Lifts an IO computation to the Compiler monad

  -- |Flag lenses
  , debug

  -- |Compiler lenses
  , flags
  , stage
  , imports
  , filename
  , src
  , tokens
  , sugaredAST
  , desugaredAST
  , tEnv
  , typedAST

  , Env
  , QEnv
  , freshTyUni
  , ungeneralise

  , debugPrint

  )
  where

import qualified Parse.Parse.AST as Parse
import qualified Parse.Desugar.AST as Desugar
import qualified Parse.Tokenise.Token as Tokenise
import qualified Check.AST as Check
import AST (Name)
import Type
import Source
import Error (Error)

import Inbuilts (inbuilts, TopDecl(..))
import Control.Monad.State hiding (get, liftIO)
import Control.Monad.Except hiding (throwError, liftIO)
import qualified Control.Monad.Except (throwError)
import Control.Lens hiding (set)
import qualified Control.Lens (set)
import Data.Maybe (fromMaybe)

data Stage = Tokenise
           | Parse
           | Desugar
           | Generate
           | Solve
           | Interpret

instance Show Stage where
  show Tokenise           = "Tokeniser"
  show Parse              = "Parser"
  show Desugar            = "Desugarer"
  show Generate           = "Inference (Constraint Generator)"
  show Solve              = "Inference (Contraint Solver)"
  show Interpret          = "Interpreter"

-- |A Context stores all in-scope variables along with their type and how many times they are used.
type Env = [(Name, (Pure, Int))]

-- |Context for top-level declarations
type QEnv = [(Name, QPure)]

type Token = Tokenise.Annotated Tokenise.Token

data Flags = Flags { _debug :: Bool }
  deriving (Show)
makeLenses ''Flags

data CompilerState = CompilerState
  { _flags        :: Flags
  , _stage        :: Stage               -- ^ Current stage of compilation
  , _freshUnis    :: [String]            -- ^ Infinite list of distinct dummy names to use for unification types
  , _freshVars    :: [String]            -- ^ Infinite list of distinct dummy names to use for phantom variables
  , _imports      :: [FilePath]          -- ^ Loaded modules
  , _filename     :: FilePath            -- ^ File path
  , _src          :: String              -- ^ Source to compile
  , _tokens       :: [Token]             -- ^ List of tokens produced by tokeniser
  , _sugaredAST   :: (Parse.AST)         -- ^ AST after parsing of tokens
  , _desugaredAST :: (Desugar.AST)       -- ^ AST after desugaring
  , _qtEnv        :: QEnv                -- ^ Type environment of top-level functions
  , _tEnv         :: Env                 -- ^ Type environment of local functions
  , _kEnv         :: ()                  -- TODO (Kind environment)
  , _typedAST     :: (Check.AST)         -- ^ AST after type inference

  {-
  , _fname    :: Maybe FilePath            -- ^ File path
  , _imports  :: [FilePath]                -- ^ Loaded modules
  , _src      :: Maybe L.Text              -- ^ File source
  , _ast      :: Maybe Syn.Module          -- ^ Frontend AST
  , _tenv     :: Env.Env                   -- ^ Typing environment
  , _kenv     :: Map.Map Name Kind         -- ^ Kind environment
  , _cenv     :: ClassEnv.ClassEnv         -- ^ Typeclass environment
  , _cast     :: Maybe Core.Module         -- ^ Core AST
  , _flags    :: Flags.Flags               -- ^ Compiler flags
  , _venv     :: CoreEval.ValEnv Core.Expr -- ^ Core interpreter environment
  , _denv     :: DataEnv.DataEnv           -- ^ Entity dictionary
  , _clenv    :: ClassEnv.ClassHier        -- ^ Typeclass hierarchy
  -}

  } deriving (Show)
makeLenses ''CompilerState

type Compiler a = ExceptT Error (StateT CompilerState IO) a

defaultFlags :: Flags
defaultFlags = Flags { _debug = True }

get :: Lens' CompilerState a -> Compiler a
get = lift . gets . view

set :: Lens' CompilerState a -> a -> Compiler ()
set l x = lift . modify $ Control.Lens.set l x

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
  , _filename     = unset "filename"
  , _src          = unset "src"
  , _tokens       = unset "tokens"
  , _sugaredAST   = unset "sugaredAST"
  , _desugaredAST = unset "desugaredAST"
  , _qtEnv        = map (\(s, t) -> (s, ty t)) inbuilts
  , _tEnv         = unset "tenv"
  , _kEnv         = unset "kenv"
  , _typedAST     = unset "typedAST"
  }
  where unset s = error ("INTERNAL COMPILER ERROR: unset " ++ s)

liftIO :: IO a -> Compiler a
liftIO = lift . lift

run :: Compiler a -> IO (Either Error a, CompilerState)
run c = runWith c initialState

runWith :: Compiler a -> CompilerState -> IO (Either Error a, CompilerState)
runWith c s = (runStateT . runExceptT) c s

-- TODO this possibly shouldnt be here
debugPrint :: Show a => a -> Compiler ()
debugPrint x = do
  b <- get (flags . debug)
  if b then do
    s <- get stage
    liftIO $ putStrLn ("Output from stage: " ++ show s)
    liftIO $ print x
    liftIO $ putStrLn ""
    return ()
  else
    return ()


fresh :: String -> [String]
fresh alpha = concatMap perm [1..]
  where perm :: Int -> [String]
        perm 1 = map (:[]) alpha
        perm n = do { x <- alpha; y <- perm (n-1); return (x:y) }

-- TODO: Stuff below this probably shouldn't be here...
freshTyUni :: Compiler Pure
freshTyUni = do
  (x:xs) <- get freshUnis
  set freshUnis xs
  return (TyUni x)

-- TODO: Allow quantified effects
ungeneralise :: QPure -> Compiler ([Constraint], Pure)
ungeneralise (Forall cs as t) = do
  bs <- sequence (replicate (length as) freshTyUni)
  let ft = (`lookup` (zip as bs))
  let fe = const Nothing
  let subsP = subsPure ft fe
  return (map (\c -> case c of Class s t -> Class s (subsP t)) cs, subsP t)
