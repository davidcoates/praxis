{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}

module Praxis
  ( Praxis
  , PraxisT(..)
  , PraxisState
  , Stage(..)
  , emptyState

  , KEnv(..)
  , TEnv(..)
  , DAEnv(..)
  , VEnv(..)

  , throw
  , throwAt

  , save
  , try

  , runPraxis
  , runInternal

  -- |Lift an IO computation to the Praxis monad
  , liftIO

  -- |Flag lenses
  , debug
  , interactive

  -- |Praxis lenses
  , filename
  , flags
  , stage
  , kEnv
  , tEnv
  , daEnv
  , vEnv
  , system

  , freshUniT
  , freshUniK
  , freshVar
  , reuse

  , clear
  , output
  )
  where

import qualified Check.System                 as Check (System)
import           Common
import           Record                       (Record)
import           Stage
import           Term

import Env.Env
import Env.LEnv
import Value
import           Control.Applicative          (empty, liftA2)
import           Control.Concurrent
import           Control.Lens                 (Lens', makeLenses, traverseOf)
import           Control.Monad.Trans.Class    (MonadTrans (..))
import qualified Control.Monad.Trans.State    as State (get, modify, put)
import           Data.Maybe                   (fromMaybe)
import qualified Data.Set                     as Set
import qualified System.Console.Terminal.Size as Terminal
import           System.IO.Unsafe             (unsafePerformIO)

data Flags = Flags
  { _debug       :: Bool
  , _interactive :: Bool
  , _static      :: Bool              -- ^Set for internal pure computations evaluated at compile time
  } deriving (Show)

data Fresh = Fresh
  { _freshUniTs :: [String]
  , _freshUniEs :: [String]
  , _freshUniKs :: [String]
  , _freshVars  :: [String]
  }

instance Show Fresh where
  show _ = "<fresh>"

type VEnv = Env Name Value

type TEnv = LEnv Name (Typed QType)

type KEnv = Env Name (Kinded Kind)

type DAEnv = Env Name (Typed DataAlt)

data PraxisState = PraxisState
  { _filename :: String              -- ^File path (for error messages)
  , _flags    :: Flags               -- ^Flags
  , _fresh    :: Fresh
  , _stage    :: Stage               -- ^Current stage of compilation
  , _kEnv     :: KEnv                -- ^Kind environment
  , _tEnv     :: TEnv                -- ^Type environment
  , _daEnv    :: DAEnv               -- ^Data alternative environment
  , _vEnv     :: VEnv                -- ^Value environment for interpreter
  , _system   :: Check.System        -- ^ TODO rename?
  }

instance Show PraxisState where
  show s = "<praxis state>"

type Praxis = MaybeT (StateT PraxisState IO)

newtype PraxisT f a = PraxisT { runPraxisT :: f (Praxis a) }

instance MonadTrans PraxisT where
  lift x = PraxisT (pure <$> x)

instance Functor f => Functor (PraxisT f) where
  fmap f (PraxisT x) = PraxisT (fmap (fmap f) x)

defaultFlags :: Flags
defaultFlags = Flags { _debug = False, _interactive = False, _static = False }

defaultFresh = Fresh
  { _freshUniTs   = map (("?t"++) . show) [0..]
  , _freshUniEs   = map (("?e"++) . show) [0..]
  , _freshUniKs   = map (("?k"++) . show) [0..]
  , _freshVars    = map (("?x"++) . show) [0..]
  }

emptyState :: PraxisState
emptyState = PraxisState
  { _filename     = "<stdin>"
  , _flags        = defaultFlags
  , _fresh        = defaultFresh
  , _stage        = Unknown
  , _kEnv         = unset "kEnv"
  , _tEnv         = unset "tEnv"
  , _daEnv        = unset "daEnv"
  , _vEnv         = unset "vEnv"
  , _system       = unset "system"
  }
  where unset s = error ("unset " ++ s)

makeLenses ''Flags
makeLenses ''Fresh
makeLenses ''PraxisState

throw :: Pretty a => a -> Praxis b
throw x = display (Style Bold (Fg DullRed "error: ") <> pretty x) >> empty

throwAt :: Pretty a => Source -> a -> Praxis b
throwAt s x = display (Style Bold (pretty s) <> " " <> Style Bold (Fg DullRed "error: ") <> pretty x) >> empty

display :: Pretty a => a -> Praxis ()
display x = try p >> return () where
  p = do
    s <- use stage
    t <- liftIO $ getTerm
    liftIO $ printColoredS t $ "\n{- " <> Style Italic (plain (show s)) <> " -}\n\n"
    liftIO $ printColoredS t $ pretty x <> "\n"

save :: Lens' PraxisState a -> Praxis b -> Praxis b
save l c = do
  x <- use l
  r <- c
  l .= x
  return r

try :: Praxis a -> Praxis (Maybe a)
try p = do
  s <- lift State.get
  (x, t) <- liftIO $ runPraxis p s
  case x of
    Nothing -> lift (State.put s) >> return Nothing
    Just y  -> lift (State.put t) >> return (Just y)

runInternal :: PraxisState -> Praxis a -> a
runInternal s c = case fst $ unsafePerformIO (runPraxis c' s) of
  Nothing -> error "static computation failed"
  Just x  -> x
  where c' = (flags . static .= True) >> c

assert :: Lens' PraxisState a -> (a -> Bool) -> String -> Praxis b -> Praxis b
assert l p s c = do
  x <- use l
  if p x then c else error s

liftIO :: IO a -> Praxis a
liftIO io = do
  s <- use (flags . static)
  -- If the static flag is set, we must not perform IO
  if s then empty else lift (lift io)

runPraxis :: Praxis a -> PraxisState -> IO (Maybe a, PraxisState)
runPraxis = runStateT . runMaybeT

clear :: Praxis ()
clear = do
  d <- use (flags . debug)
  when d $ liftIO $ do
    putStrLn ""
    Terminal.size >>= \case
      Just (Terminal.Window _ w) -> putStrLn $ replicate w '='
      Nothing                    -> pure ()

output :: Pretty a => a -> Praxis ()
output x = do
  d <- use (flags . debug)
  when d $ display x

freshUniT :: Praxis (Typed Type)
freshUniT = do
  (x:xs) <- use (fresh . freshUniTs)
  fresh . freshUniTs .= xs
  return ((Phantom, (Phantom, ()) :< KindType) :< TyUni x)

freshUniK :: Praxis (Kinded Kind)
freshUniK = do
  (k:ks) <- use (fresh . freshUniKs)
  fresh . freshUniKs .= ks
  return ((Phantom, ()) :< KindUni k)

freshVar :: Praxis Name
freshVar = do
  (x:xs) <- use (fresh . freshVars)
  fresh . freshVars .= xs
  return x

-- This will fuck things up if the name is still used somewhere
reuse :: Name -> Praxis ()
reuse _ = pure ()
{-
reuse n@('?':c:_) = over (fresh . f c) (n:)
  where f 'a' = freshUniTs
        f 'e' = freshUniEs
        f 'k' = freshUniKs
-}

