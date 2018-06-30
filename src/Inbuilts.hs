module Inbuilts
  ( initialState
  , ty
  ) where

import           Control.Lens (set)

import           AST          (Lit (..))
import           Compiler     (CompilerState, emptyState, liftIO, qtEnv,
                               runStatic, tEnv, vEnv)
import           Env.QTEnv    (QTEnv)
import qualified Env.QTEnv    as QTEnv (fromList)
import           Env.TEnv     (TEnv)
import qualified Env.TEnv     as TEnv (fromList)
import           Env.VEnv     (VEnv)
import qualified Env.VEnv     as VEnv (fromList)
import           Error
import           Parse        (parseFree)
import           Record
import           Source       (Source)
import           Tag
import           Type
import           Value

initialState :: CompilerState
initialState = set tEnv initialTEnv $ set vEnv initialVEnv $ emptyState

ty :: String -> Pure
ty s = let (_ :< t :# _) = runStatic (parseFree s) :: Tag Source Type in t

prelude :: [(Name, Pure, Value)]
prelude =
  [ ("add",      ty "(Int, Int) -> Int",     lift (+))
  , ("sub",      ty "(Int, Int) -> Int",     lift (-))
  , ("mul",      ty "(Int, Int) -> Int",     lift (*))
  , ("getInt",   ty "() -> Int # StdIn",     F (\(R _) -> liftIO ((L . Int) <$> readLn)))
  , ("putInt",   ty "Int -> () # StdOut",    F (\(L (Int x)) -> liftIO (print x >> pure (R unit))))
  , ("putStrLn", ty "String -> () # StdOut", F (\(L (String x)) -> liftIO (putStrLn x >> pure (R unit))))
  ]
  where lift :: (Int -> Int -> Int) -> Value
        lift f = F (\(R r) -> case unpair r of (L (Int a), L (Int b)) -> pure (L (Int (f a b))))

--  ("dot", F (\(R r) -> case unpair r of (F f, F g) -> pure (F (\x -> g x >>= f))))

initialVEnv :: VEnv
initialVEnv = VEnv.fromList (map (\(n, _, v) -> (n, v)) prelude)

initialTEnv :: TEnv
initialTEnv = TEnv.fromList (map (\(n, t, _) -> (n, t)) prelude)

