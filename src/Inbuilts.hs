{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE QuasiQuotes      #-}
{-# LANGUAGE Rank2Types       #-}

module Inbuilts
  ( initialState
  ) where

import           Common
import qualified Env.Env                   as Env
import qualified Env.LEnv                  as LEnv
import           Introspect
import           Parse                     (parse)
import           Praxis
import           Term                      hiding (Lit (..), Pair, Unit)
import           Value

import           Control.Monad.Trans.Class (MonadTrans (..))
import qualified Control.Monad.Trans.State as State (get)
import qualified Data.Set                  as Set
import           Text.RawString.QQ

-- Include inbuilt kinds
initialState0 :: PraxisState
initialState0 = set dtEnv initialDTEnv $ set kEnv initialKEnv $ emptyState

-- Include inbuilts
initialState1 :: PraxisState
initialState1 = set vEnv initialVEnv $ set tEnv initialTEnv $ initialState0

-- TODO Make this importPrelude, a Monadic action?
initialState :: PraxisState
initialState = fixup (runInternal initialState1 ((parse prelude :: Praxis (Annotated Program)) >> lift State.get)) where
  -- TODO a nicer way to do this. Undo all the things except the fields we care about.
  fixup = set flags (view flags emptyState) . set fresh (view fresh emptyState) . set stage (view stage emptyState) . set kindSystem (view kindSystem emptyState) . set tySystem (view tySystem emptyState)

mono :: String -> Annotated Type
mono s = runInternal initialState0 (parse s :: Praxis (Annotated Type))

poly :: String -> Annotated QType
poly s = runInternal initialState0 (parse s :: Praxis (Annotated QType))

kind :: String -> Annotated Kind
kind s = runInternal emptyState (parse s :: Praxis (Annotated Kind))

inbuilts :: [(Name, Annotated QType, Value)]
inbuilts =
  [ ("add" ,     poly "forall a | Integral a . (a, a) -> a", liftI (+)) -- TODO should be Num, not Integral
  , ("subtract", poly "forall a | Integral a . (a, a) -> a", liftI (-))
  , ("multiply", poly "forall a | Integral a . (a, a) -> a", liftI (*))
  , ("negate",   poly "forall a | Integral a . a -> a",
      Fun (\(Int x) -> pure (Int (negate x))))
  , ("get_int",      poly "() -> Int",
      Fun (\Unit -> liftIOUnsafe (Int <$> readLn)))
  , ("get_str", poly "() -> String",
      Fun (\Unit -> Value.String <$> liftIOUnsafe getContents)) -- TODO need to make many of these functions strict?
  , ("put_int",      poly "Int -> ()",
      Fun (\(Int x) -> liftIOUnsafe (print x >> pure Unit)))
  , ("put_str",      poly "forall &r. &r String -> ()",
      Fun (\(String s) -> liftIOUnsafe (putStr s) >> pure Unit))
  , ("put_str_ln",   poly "forall &r. &r String -> ()",
      Fun (\(String s) -> liftIOUnsafe (putStrLn s) >> pure Unit))
  , ("compose",      poly "forall a b c. (b -> c, a -> b) -> a -> c",
      Fun (\(Pair (Fun f) (Fun g)) -> pure (Fun (\x -> g x >>= f))))
  , ("print",        poly "forall &r a. &r a -> ()",
      Fun (\x -> liftIOUnsafe (print x >> pure Unit))) -- TODO should have Show constraint
  , ("new_array",    poly "forall a. (Int, () -> a) -> Array a",
      Fun (\(Pair (Int i) v) -> Value.newArray i v))
  , ("at_array",     poly "forall &r a. (&r Array a, Int) -> &r a",
      Fun (\(Pair (Array a) (Int i)) -> Value.readArray a i))
  , ("len_array",    poly "forall &r a. &r Array a -> Int",
      Fun (\(Array a) -> Value.Int <$> Value.lenArray a))
  , ("set_array",    poly "forall a. (Array a, Int, a) -> Array a",
      Fun (\(Pair (Array a) (Pair (Int i) e)) -> Value.writeArray a i e >> pure (Array a)))
  , ("not",          poly "Bool -> Bool", Fun (\(Bool a) -> pure (Bool (not a))))
  , ("or",           poly "(Bool, Bool) -> Bool", liftB (||))
  , ("and",  poly "(Bool, Bool) -> Bool", liftB (&&))
  , ("eq",       poly "forall a | Integral a . (a, a) -> Bool", liftE (==)) -- TODO should be Eq, not Integral
  , ("neq",      poly "forall a | Integral a . (a, a) -> Bool", liftE (/=))
  , ("lt",       poly "forall a | Integral a . (a, a) -> Bool", liftE (<)) -- TODO should be Ord, not Integral
  , ("gt",       poly "forall a | Integral a . (a, a) -> Bool", liftE (>))
  , ("lte",      poly "forall a | Integral a . (a, a) -> Bool", liftE (<=))
  , ("gte",      poly "forall a | Integral a . (a, a) -> Bool", liftE (>=))
  ]
  where
    liftI :: Integral a => (a -> a -> a) -> Value
    liftI f = undefined -- TODO
    liftE :: Integral a => (a -> a -> Bool) -> Value
    liftE f = undefined
    liftB :: (Bool -> Bool -> Bool) -> Value
    liftB f = Fun (\(Pair (Bool a) (Bool b)) -> pure (Bool (f a b)))

inbuiltKinds :: [(Name, Annotated Kind)]
inbuiltKinds =
  [
  -- Types
    ("Array",    kind "Type -> Type")
  , ("Bool",     kind "Type")
  , ("Char",     kind "Type")
  , ("I8",       kind "Type")
  , ("I16",      kind "Type")
  , ("I32",      kind "Type")
  , ("I64",      kind "Type")
  , ("ISize",    kind "Type")
  , ("String",   kind "Type")
  , ("U8",       kind "Type")
  , ("U16",      kind "Type")
  , ("U32",      kind "Type")
  , ("U64",      kind "Type")
  , ("USize",    kind "Type")
  -- Constraints
  , ("Copy",     kind "Type -> Constraint")
  , ("Integral", kind "Type -> Constraint")
  ]

initialDTEnv :: DTEnv
initialDTEnv = Env.fromList
  [ ("Array",  \(Just _) -> CanNotCopy)
  , ("Bool",   \Nothing  -> CanCopy)
  , ("Char",   \Nothing  -> CanCopy)
  , ("I8",     \Nothing  -> CanCopy)
  , ("I16",    \Nothing  -> CanCopy)
  , ("I32",    \Nothing  -> CanCopy)
  , ("I64",    \Nothing  -> CanCopy)
  , ("ISize",  \Nothing  -> CanCopy)
  , ("U8",     \Nothing  -> CanCopy)
  , ("U16",    \Nothing  -> CanCopy)
  , ("U32",    \Nothing  -> CanCopy)
  , ("U64",    \Nothing  -> CanCopy)
  , ("USize",  \Nothing  -> CanCopy)
  , ("String", \Nothing  -> CanNotCopy)
  ]

initialKEnv :: KEnv
initialKEnv = Env.fromList inbuiltKinds

initialTEnv :: TEnv
initialTEnv = LEnv.fromList (map (\(n, t, _) -> (n, t)) inbuilts)

initialVEnv :: VEnv
initialVEnv = Env.fromList (map (\(n, _, v) -> (n, v)) inbuilts)

-- TODO interfaces
prelude = [r|

-- Operators
operator (_ + _) = add where
  left associative

operator (_ - _) = subtract where
  left associative
  precedence equal (_ + _)

operator (_ * _) = multiply where
  left associative
  precedence above (_ + _)

operator (- _) = negate where
  precedence above (_ * _)

operator (_ . _) = compose where
  right associative

operator (_ [ _ ]) = at_array

operator (_ [ _ ] <- _) = set_array

operator (! _) = not

operator (_ && _) = and where
  left associative
  precedence below (! _)

operator (_ || _) = or where
  left associative
  precedence below (_ && _)

operator (_ == _) = eq where
  precedence below (_ + _)

operator (_ != _) = neq where
  precedence equal (_ == _)

operator (_ < _) = lt where
  precedence equal (_ == _)

operator (_ > _) = gt where
  precedence equal (_ == _)

operator (_ <= _) = lte where
  precedence equal (_ == _)

operator (_ >= _) = gte where
  precedence equal (_ == _)

|]
