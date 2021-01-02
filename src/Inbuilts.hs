{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE Rank2Types       #-}

module Inbuilts
  ( initialState
  ) where

import           Common
import           Env
import           Introspect
import           Parse           (parse)
import           Praxis
import           Term            hiding (Lit (..), Pair, Unit)
import           Value

import           Data.Array      (array)
import           Data.List       (nub, sort)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map (empty, fromList, singleton)
import qualified Data.Set        as Set (empty)

-- TODO Make this importPrelude, a Monadic action?
initialState :: PraxisState
initialState = set tSynonyms initialTSynonyms $ set opContext initialOpContext $ set tEnv initialTEnv $ set vEnv initialVEnv $ set kEnv initialKEnv $ set daEnv initialDAEnv $ emptyState

mono :: String -> Annotated Type
mono s = runInternal initialState (parse s :: Praxis (Annotated Type))

poly :: String -> Annotated QType
poly s = runInternal initialState (parse s :: Praxis (Annotated QType))

kind :: String -> Annotated Kind
kind s = runInternal initialState (parse s :: Praxis (Annotated Kind))

prelude :: [(Name, Annotated QType, Value)]
prelude =
  [ ("add" ,         poly "(Int, Int) -> Int", liftI (+))
  , ("subtract",     poly "(Int, Int) -> Int", liftI (-))
  , ("multiply",     poly "(Int, Int) -> Int", liftI (*))
  , ("negate",       poly "Int -> Int",
      Fun (\(Int x) -> pure (Int (negate x))))
  , ("get_int",      poly "() -> Int",
      Fun (\Unit -> liftIO (Int <$> readLn)))
  , ("get_contents", poly "() -> Array Char",
      Fun (\Unit -> liftIO getContents >>= (\s -> Value.Array <$> (Value.fromString s)))) -- TODO need to make many of these functions strict?
  , ("put_int",      poly "Int -> ()",
      Fun (\(Int x) -> liftIO (print x >> pure Unit)))
  , ("put_str",      poly "&Array Char -> ()",
      Fun (\(Array a) -> Value.toString a >>= (\s -> liftIO (putStr s)) >> pure Unit))
  , ("put_str_ln",   poly "&Array Char -> ()",
      Fun (\(Array a) -> Value.toString a >>= (\s -> liftIO (putStrLn s)) >> pure Unit))
  , ("compose",      poly "forall a b c. (b -> c, a -> b) -> a -> c",
      Fun (\(Pair (Fun f) (Fun g)) -> pure (Fun (\x -> g x >>= f))))
  , ("print",        poly "forall a. &a -> ()",
      Fun (\x -> liftIO (print x >> pure Unit))) -- TODO should have Show constraint
  , ("at",           poly "forall a. (&Array a, Int) -> a",
      Fun (\(Pair (Array a) (Int i)) -> Value.readArray a i))
  , ("len",          poly "forall a. &Array a -> Int",
      Fun (\(Array a) -> Value.Int <$> Value.len a))
  , ("set",          poly "forall a. (Array a, Int, a) -> Array a",
      Fun (\(Pair (Array a) (Pair (Int i) e)) -> Value.writeArray a i e >> pure (Array a)))
  , ("or",           poly "(Bool, Bool) -> Bool", liftB (||))
  , ("and",          poly "(Bool, Bool) -> Bool", liftB (&&))
  ]
  where
    liftI :: (Int -> Int -> Int) -> Value
    liftI f = Fun (\(Pair (Int a) (Int b)) -> pure (Int (f a b)))
    liftB :: (Bool -> Bool -> Bool) -> Value
    liftB f = Fun (\(Pair (Bool a) (Bool b)) -> pure (Bool (f a b)))

preludeKinds :: [(Name, Annotated Kind)]
preludeKinds =
  [ ("Int",    kind "Type")
  , ("Bool",   kind "Type")
  , ("String", kind "Type")
  , ("Char",   kind "Type")
  , ("Array",  kind "Type -> Type")
  , ("Share",  kind "Type -> Constraint")
--  , ("->",     kind "Type -> Type -> Type")
  ]

initialVEnv :: VEnv
initialVEnv = fromList (map (\(n, _, v) -> (n, v)) prelude)

initialTEnv :: TEnv
initialTEnv = fromList (map (\(n, t, _) -> (n, t)) prelude)

initialKEnv :: KEnv
initialKEnv = fromList preludeKinds

initialDAEnv :: DAEnv
initialDAEnv = empty

preludeOps = unlines $
  [ "operator (_ + _) = add where"
  , "  associates left"
  , ""
  , "operator (_ - _) = subtract where"
  , "  associates left"
  , "  precedence equal (_ + _)"
  , ""
  , "operator (_ * _) = multiply where"
  , "  associates left"
  , "  precedence above (_ + _)"
  , ""
  , "operator (- _) = negate where"
  , "  precedence above (_ * _)"
  , ""
  , "operator (_ . _) = compose where"
  , "  associates right"
  , ""
  , "operator (_ [ _ ]) = at"
  , ""
  , "operator (_ [ _ ] <- _) = set"
  , ""
  , "operator (_ || _) = or"
  , ""
  , "operator (_ && _) = and"
  ]

initialOpContext :: OpContext
initialOpContext = runInternal (set opContext emptyOpContext $ set vEnv initialVEnv $ emptyState) ((parse preludeOps :: Praxis (Annotated Program)) >> use opContext)

emptyOpContext :: OpContext
emptyOpContext = OpContext { _defns = Map.empty, _prec = array (0, -1) [], _levels = [] }

initialTSynonyms :: Map Name (Annotated Type)
initialTSynonyms = Map.singleton "String" (mono "Array Char")
