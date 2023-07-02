{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE QuasiQuotes      #-}
{-# LANGUAGE Rank2Types       #-}

module Inbuilts
  ( initialState
  , inbuiltInclude
  ) where

import           Common
import           Control.Lens              (set, view)
import           Env
import           Interpret.Value           as Value
import           Introspect
import           Parse                     (parse)
import           Praxis
import           Term                      hiding (Lit (..), Pair, Unit)
import           Text.RawString.QQ

import           Control.Monad.Trans.Class (MonadTrans (..))
import qualified Control.Monad.Trans.State as State (get)

-- Include inbuilt kinds
initialState0 :: PraxisState
initialState0 = set kEnv initialKEnv $ emptyState

-- Include inbuilts
initialState1 :: PraxisState
initialState1 = set vEnv initialVEnv $ set tEnv initialTEnv $ initialState0

-- TODO Make this importPrelude, a Monadic action?
initialState :: PraxisState
initialState = fixup (runInternal initialState1 ((parse prelude :: Praxis (Annotated Program)) >> lift State.get)) where
  -- TODO a nicer way to do this. Undo all the things except the fields we care about.
  fixup = set outfile (view outfile emptyState) . set infile (view infile emptyState) . set flags (view flags emptyState) . set fresh (view fresh emptyState) . set stage (view stage emptyState) . set system (view system emptyState)

mono :: String -> Annotated Type
mono s = runInternal initialState0 (parse s :: Praxis (Annotated Type))

poly :: String -> Annotated QType
poly s = runInternal initialState0 (parse s :: Praxis (Annotated QType))

kind :: String -> Annotated Kind
kind s = runInternal emptyState (parse s :: Praxis (Annotated Kind))

inbuilts :: [(Name, Annotated QType, Value)]
inbuilts =
  [ ("add_int" ,     poly "(Int, Int) -> Int", liftI (+))
  , ("subtract_int", poly "(Int, Int) -> Int", liftI (-))
  , ("multiply_int", poly "(Int, Int) -> Int", liftI (*))
  , ("negate_int",   poly "Int -> Int",
      Fun (\(Int x) -> pure (Int (negate x))))
  , ("unary_plus_int",   poly "Int -> Int",
      Fun (\(Int x) -> pure (Int x)))
  , ("get_int",      poly "() -> Int",
      Fun (\Unit -> liftIO (Int <$> readLn)))
  , ("get_contents", poly "() -> String",
      Fun (\Unit -> liftIO (Value.String <$> getContents)))-- TODO need to make many of these functions strict?
  , ("put_int",      poly "Int -> ()",
      Fun (\(Int x) -> liftIO (print x >> pure Unit)))
  , ("put_str",      poly "&String -> ()",
      Fun (\(String s) -> liftIO (putStr s) >> pure Unit))
  , ("put_str_ln",   poly "&String -> ()",
      Fun (\(String s) -> liftIO (putStrLn s) >> pure Unit))
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
  , ("eq_int",       poly "(Int, Int) -> Bool", liftE (==)) -- TODO use modules
  , ("neq_int",      poly "(Int, Int) -> Bool", liftE (/=))
  , ("lt_int",       poly "(Int, Int) -> Bool", liftE (<))
  , ("gt_int",       poly "(Int, Int) -> Bool", liftE (>))
  , ("lte_int",      poly "(Int, Int) -> Bool", liftE (<=))
  , ("gte_int",      poly "(Int, Int) -> Bool", liftE (>=))
  ]
  where
    liftI :: (Int -> Int -> Int) -> Value
    liftI f = Fun (\(Pair (Int a) (Int b)) -> pure (Int (f a b)))
    liftB :: (Bool -> Bool -> Bool) -> Value
    liftB f = Fun (\(Pair (Bool a) (Bool b)) -> pure (Bool (f a b)))
    liftE :: (Int -> Int -> Bool) -> Value
    liftE f = Fun (\(Pair (Int a) (Int b)) -> pure (Bool (f a b)))


inbuiltKinds :: [(Name, Annotated Kind)]
inbuiltKinds =
  [ ("Int",    kind "Type")
  , ("Bool",   kind "Type")
  , ("String", kind "Type")
  , ("Char",   kind "Type")
  , ("Array",  kind "Type -> Type")
  , ("String", kind "Type") -- TODO make this a synonym
  , ("Share",  kind "Type -> Constraint")
  ]

initialVEnv :: VEnv
initialVEnv = fromList (map (\(n, _, v) -> (n, v)) inbuilts)

initialTEnv :: TEnv
initialTEnv = fromList (map (\(n, t, _) -> (n, t)) inbuilts)

initialKEnv :: KEnv
initialKEnv = fromList inbuiltKinds

-- TODO interfaces
prelude = [r|

-- Operators
operator (_ + _) = add_int where
  left associative

operator (_ - _) = subtract_int where
  left associative
  precedence equal (_ + _)

operator (_ * _) = multiply_int where
  left associative
  precedence above (_ + _)

operator (- _) = negate_int where
  precedence above (_ * _)

operator (+ _) = unary_plus_int where
  precedence equal (- _)

operator (_ . _) = compose where
  right associative

operator (_ [ _ ]) = at

operator (_ [ _ ] <- _) = set

operator (_ || _) = or

operator (_ && _) = and

operator (_ == _) = eq_int where
  precedence below (_ + _)

operator (_ != _) = neq_int where
  precedence equal (_ == _)

operator (_ < _) = lt_int where
  precedence equal (_ == _)

operator (_ > _) = gt_int where
  precedence equal (_ == _)

operator (_ <= _) = lte_int where
  precedence equal (_ == _)

operator (_ >= _) = gte_int where
  precedence equal (_ == _)

|]

-- TODO
inbuiltInclude :: String
inbuiltInclude = [r|

#include <iostreamm>

int add_int(int x, int y) { return x + y; }
int subtract_int(int, x int y) { return x - y; }
int eq_int(int, x int y) { return x == y; }

int get_int() { int x; std::cin >> x; return x; }
std::string get_contents() { std::string s; std::cin >> s; return s; }

void put_int(int x) { std::cout << x; }
void put_str(const std::string& s) { std::cout << s; }
void put_str_ln(const std::string& s) { std::cout << s << std::endl; }

|]
