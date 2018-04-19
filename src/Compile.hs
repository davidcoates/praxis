{-# LANGUAGE TemplateHaskell, RankNTypes #-}

module Compile
  ( Compiler
  , CompilerState
  , initialState
  , throwError
  , Stage(..)

  , get
  , set

  -- ^ Compiler lenses
  , stage
  , imports
  , filename
  , src
  , tokens
  , sugaredAST
  , desugaredAST
  , tEnv
  , typedAST

  , filenameDisplay

  , Env
  , QEnv
  , freshTyUni
  , ungeneralise

  , run
  )
  where

import qualified Parse.Parse.AST as Parse
import qualified Parse.Desugar.AST as Desugar
import qualified Parse.Tokenise.Token as Tokenise
import qualified Check.AST as Check
import Pos
import AST (Name)
import Type
import Inbuilts (inbuilts, TopDecl(..))
import Control.Monad.State hiding (get)
import Control.Monad.Except hiding (throwError)
import qualified Control.Monad.Except (throwError)
import Control.Lens hiding (set)
import qualified Control.Lens (set)
import Data.Maybe (fromMaybe)

type Compiler e a = ExceptT e (StateT CompilerState IO) a

data Stage = Tokenise
           | Parse
           | Desugar
           | Generate
           | Solve
           | Interpret

instance Show Stage where
  show Tokenise           = "tokenising"
  show Parse              = "parsing"
  show Desugar            = "desugaring"
  show Generate           = "inference(generation)"
  show Solve              = "inference(solving)"
  show Interpret          = "interpreting"

-- |A Context stores all in-scope variables along with their type and how many times they are used.
type Env = [(Name, (Pure, Int))]

-- |Context for top-level declarations
type QEnv = [(Name, QPure)]

data CompilerState = CompilerState
  { _stage        :: Maybe Stage               -- ^ Current stage of compilation
  , _freshUnis    :: Maybe [String]            -- ^ Infinite list of distinct dummy names to use for unification types
  , _freshVars    :: Maybe [String]            -- ^ Infinite list of distinct dummy names to use for phantom variables
  , _imports      :: Maybe [FilePath]          -- ^ Loaded modules
  , _filename     :: Maybe FilePath            -- ^ File path
  , _src          :: Maybe String              -- ^ Source to compile
  , _tokens       :: Maybe [Tokenise.Token]    -- ^ List of tokens produced by tokeniser
  , _sugaredAST   :: Maybe (Parse.AST)         -- ^ AST after parsing of tokens
  , _desugaredAST :: Maybe (Desugar.AST)       -- ^ AST after desugaring
  , _qtEnv        :: Maybe QEnv                -- ^ Type environment of top-level functions
  , _tEnv         :: Maybe Env                 -- ^ Type environment of local functions
  , _kEnv         :: Maybe ()                  -- TODO (Kind environment)
  , _typedAST     :: Maybe (Check.AST)         -- ^ AST after type inference

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

getRaw :: Lens' CompilerState a -> Compiler e a
getRaw l = lift (gets (view l))

get :: Lens' CompilerState (Maybe a) -> Compiler e a
get l = fromMaybe <$> getRaw l
  where fromMaybe (Just x) = x

set :: Lens' CompilerState (Maybe a) -> a -> Compiler e ()
set l x = lift (modify (Control.Lens.set l (Just x)))

throwError :: e -> Compiler e a
throwError = Control.Monad.Except.throwError

filenameDisplay :: Compiler e String
filenameDisplay = fromMaybe "<interactive>" <$> getRaw filename

initialState :: CompilerState
initialState  = CompilerState
  { _stage        = Just Parse
  , _freshUnis    = Just $ map ('~':) (fresh ['a'..'z'])
  , _freshVars    = Just $ map ('_':) (fresh ['a'..'z'])
  , _imports      = Nothing
  , _filename     = Nothing
  , _src          = Nothing
  , _tokens       = Nothing
  , _sugaredAST   = Nothing
  , _desugaredAST = Nothing
  , _qtEnv        = Just $ map (\(s, t) -> (s, ty t)) inbuilts
  , _tEnv         = Nothing
  , _kEnv         = Nothing
  , _typedAST     = Nothing
  }

run :: Compiler e a -> IO (Either e a)
run c = fst <$> (runStateT . runExceptT) c initialState

fresh :: String -> [String]
fresh alpha = concatMap perm [1..]
  where perm :: Int -> [String]
        perm 1 = map (:[]) alpha
        perm n = do { x <- alpha; y <- perm (n-1); return (x:y) }

-- TODO: Stuff below this probably shouldn't be here...
freshTyUni :: Compiler e Pure
freshTyUni = do
  (x:xs) <- get freshUnis
  set freshUnis xs
  return (TyUni x)

-- TODO: Allow quantified effects
ungeneralise :: QPure -> Compiler e ([Constraint], Pure)
ungeneralise (Forall cs as t) = do
  bs <- sequence (replicate (length as) freshTyUni)
  let ft = (`lookup` (zip as bs))
  let fe = const Nothing
  let subsP = subsPure ft fe
  return (map (\c -> case c of Class s t -> Class s (subsP t)) cs, subsP t)
