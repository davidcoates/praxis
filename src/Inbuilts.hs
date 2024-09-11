{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE QuasiQuotes      #-}
{-# LANGUAGE Rank2Types       #-}

module Inbuilts
  ( runWithPrelude
  , integral
  , clone
  , dispose
  , copy
  , capture
  ) where

import qualified Check.Type.Rename         as Rename
import           Common
import qualified Env.Lazy
import qualified Env.Linear
import qualified Env.Strict
import           Introspect
import           Parse                     (parse)
import           Praxis
import           Term                      hiding (Lit (..), Pair, Unit)
import           Value

import           Control.Monad.Trans.Class (MonadTrans (..))
import qualified Control.Monad.Trans.State as State (get)
import           Data.Map.Strict           (Map)
import qualified Data.Map.Strict           as Map
import qualified Data.Set                  as Set
import           System.IO.Unsafe          (unsafePerformIO)
import           Text.RawString.QQ


runInternal :: Praxis a -> a
runInternal c = case unsafePerformIO (runPraxis (flags . silent .= True >> c)) of
  Left e  -> error ("internal computation failed: " ++ e)
  Right x -> x

kind :: String -> Annotated Kind
kind s = runInternal (parse s :: Praxis (Annotated Kind))

initialKEnv :: KEnv
initialKEnv = Env.Strict.fromList
  [
  -- Types
    ("Array",    kind "Type -> Type")
  , ("Bool",     kind "Type")
  , ("Char",     kind "Type")
  , ("Fn",       kind "Type -> Type -> Type")
  , ("I8",       kind "Type")
  , ("I16",      kind "Type")
  , ("I32",      kind "Type")
  , ("I64",      kind "Type")
  , ("ISize",    kind "Type")
  , ("Ref",      kind "Type -> Type")
  , ("String",   kind "Type")
  , ("U8",       kind "Type")
  , ("U16",      kind "Type")
  , ("U32",      kind "Type")
  , ("U64",      kind "Type")
  , ("USize",    kind "Type")
  , ("Unit",     kind "Type")
  , ("Pair",     kind "Type -> Type -> Type")
  -- Constraints
  , ("Clone",          kind "Type -> Constraint")
  , ("Dispose",        kind "Type -> Constraint")
  , ("Copy",           kind "Type -> Constraint")
  , ("Capture",        kind "Type -> Constraint")
  , ("Integral",       kind "Type -> Constraint")
  ]


-- TODO do we actually need kinds here?

-- TODO should be replaced with instances in prelude

integral :: Annotated Type -> TypeConstraint
integral t = Instance $ TypeApply (TypeCon "Integral" `as` kind "Type -> Constraint") t `as` kind "Type"

clone :: Annotated Type -> TypeConstraint
clone t = Instance $ TypeApply (TypeCon "Clone" `as` kind "Type -> Constraint") t `as` kind "Type"

dispose :: Annotated Type -> TypeConstraint
dispose t = Instance $ TypeApply (TypeCon "Dispose" `as` kind "Type -> Constraint") t `as` kind "Type"

copy :: Annotated Type -> TypeConstraint
copy t = Instance $ TypeApply (TypeCon "Copy" `as` kind "Type -> Constraint") t `as` kind "Type"

capture :: Annotated Type -> TypeConstraint
capture t = Instance $ TypeApply (TypeCon "Capture" `as` kind "Type -> Constraint") t `as` kind "Type"

initialIEnv :: IEnv
initialIEnv = Env.Strict.fromList
  [ ("Array", Map.fromList
    [ ("Clone",   \[t] -> (Inbuilt, IsInstanceOnlyIf [clone t]))
    , ("Dispose", \[t] -> (Inbuilt, IsInstanceOnlyIf [dispose t]))
    ]
    )
  , ("Bool", primitive)
  , ("Char", primitive)
  , ("Fn", Map.fromList
    [ ("Clone",   \_ -> (Inbuilt, IsInstance))
    , ("Dispose", \_ -> (Inbuilt, IsInstance))
    , ("Copy",    \_ -> (Inbuilt, IsInstance))
    , ("Capture", \_ -> (Inbuilt, IsInstance))
    ]
    )
  , ("I8", integral)
  , ("I16", integral)
  , ("I32", integral)
  , ("I64", integral)
  , ("ISize", integral)
  , ("Pair", Map.fromList
    [ ("Clone",   \[a, b] -> (Trivial, IsInstanceOnlyIf [clone a, clone b]))
    , ("Dispose", \[a, b] -> (Trivial, IsInstanceOnlyIf [dispose a, dispose b]))
    , ("Copy",    \[a, b] -> (Trivial, IsInstanceOnlyIf [copy a, copy b]))
    , ("Capture", \[a, b] -> (Trivial, IsInstanceOnlyIf [capture a, capture b]))
    ]
    )
  , ("Ref", Map.fromList
    [ ("Clone",   \_ -> (Trivial, IsInstance))
    , ("Dispose", \_ -> (Trivial, IsInstance))
    , ("Copy",    \_ -> (Trivial, IsInstance))
    ]
    )
  , ("String", Map.fromList
    [ ("Clone",   \_ -> (Inbuilt, IsInstance))
    , ("Dispose", \_ -> (Inbuilt, IsInstance))
    ]
    )
  , ("U8", integral)
  , ("U16", integral)
  , ("U32", integral)
  , ("U64", integral)
  , ("USize", integral)
  , ("Unit", primitive)
  ] where
    primitive = Map.fromList
      [ ("Clone",   \_ -> (Trivial, IsInstance))
      , ("Dispose", \_ -> (Trivial, IsInstance))
      , ("Copy",    \_ -> (Trivial, IsInstance))
      , ("Capture", \_ -> (Trivial, IsInstance))
      ]
    integral = primitive `Map.union` Map.fromList
      [ ("Integral", \_ -> (Inbuilt, IsInstance))
      ]


inbuilts :: [(Name, Annotated QType, Value)]
inbuilts =
  [ ("add"
    , poly "forall a | Integral a. (a, a) -> a" -- TODO should be Num, not Integral
    , liftIII (+)
    )
  , ("subtract"
    , poly "forall a | Integral a. (a, a) -> a"
    , liftIII (-)
    )
  , ("multiply"
    , poly "forall a | Integral a. (a, a) -> a"
    , liftIII (*)
    )
  , ("negate"
    , poly "forall a | Integral a. a -> a"
    , liftI $ \(con, decon) -> Fn (\x -> return (con (negate (decon x))))
    )
  , ("get_int"
    , poly "forall a | Integral a. () -> a"
    , liftI $ \(con, decon) -> Fn (\Unit -> liftIOUnsafe (con <$> readLn))
    )
  , ("get_str"
    , poly "() -> String"
    , Fn (\Unit -> Value.String <$> liftIOUnsafe getContents) -- TODO need to make many of these functions strict?
    )
  , ("put_int"
    , poly "forall a | Integral a. a -> ()"
    , liftI $ \(_, decon) -> Fn (\i -> liftIOUnsafe (print (decon i) >> pure Unit))
    )
  , ("put_str"
    , poly "forall &r. &r String -> ()"
    , Fn (\(String s) -> liftIOUnsafe (putStr s) >> pure Unit)
    )
  , ("put_str_ln"
    , poly "forall &r. &r String -> ()"
    , Fn (\(String s) -> liftIOUnsafe (putStrLn s) >> pure Unit)
    )
  , ("compose"
    , poly "forall a b c. (b -> c, a -> b) -> a -> c"
    , Fn (\(Pair (Fn f) (Fn g)) -> pure (Fn (\x -> g x >>= f)))
    )
  , ("print"
    , poly "forall &r a. &r a -> ()" -- TODO should have Show constraint
    , Fn (\x -> liftIOUnsafe (print x >> pure Unit))
    )
  , ("new_array"
    , poly "forall a. (USize, () -> a) -> Array a"
    , Fn (\(Pair (USize i) v) -> Value.newArray i v)
    )
  , ("at_array"
    , poly "forall &r a. (&r Array a, USize) -> &r a"
    , Fn (\(Pair (Array a) (USize i)) -> Value.readArray a i)
    )
  , ("len_array"
    , poly "forall &r a. &r Array a -> USize"
    , Fn (\(Array a) -> USize <$> Value.lenArray a)
    )
  , ("set_array"
    , poly "forall a. (Array a, USize, a) -> Array a"
    , Fn (\(Pair (Array a) (Pair (USize i) e)) -> Value.writeArray a i e >> pure (Array a))
    )
  , ("not"
    , poly "Bool -> Bool"
    , Fn (\(Bool a) -> pure (Bool (not a)))
    )
  , ("or"
    , poly "(Bool, Bool) -> Bool"
    , liftBBB (||)
    )
  , ("and"
    , poly "(Bool, Bool) -> Bool"
    , liftBBB (&&)
    )
  , ("eq"
    , poly "forall a | Integral a. (a, a) -> Bool" -- TODO should be Eq, not Integral
    , liftIIB (==)
    )
  , ("neq"
    , poly "forall a | Integral a. (a, a) -> Bool"
    , liftIIB (/=)
    )
  , ("lt"
    , poly "forall a | Integral a. (a, a) -> Bool" -- TODO should be Ord, not Integral
    , liftIIB (<)
    )
  , ("gt"
    , poly "forall a | Integral a. (a, a) -> Bool"
    , liftIIB (>)
    )
  , ("lte"
    , poly "forall a | Integral a. (a, a) -> Bool"
    , liftIIB (<=)
    )
  , ("gte"
    , poly "forall a | Integral a. (a, a) -> Bool"
    , liftIIB (>=)
    )
  ]
  where
    liftI :: ((Integer -> Value, Value -> Integer) -> Value) -> Value
    liftI f = Polymorphic $ \[(_, _ :< TypeCon ty)] -> f (integerToValue ty, valueToInteger)
    liftII :: (forall a. Integral a => (a -> a)) -> Value
    liftII f = liftI $ \(con, decon) -> Fn (\x -> return (con (f (decon x))))
    liftIII :: (forall a. Integral a => (a -> a -> a)) -> Value
    liftIII f = liftI $ \(con, decon) -> Fn (\(Pair x y) -> return (con (f (decon x) (decon y))))
    liftIIB :: (forall a. Integral a => (a -> a -> Bool)) -> Value
    liftIIB f = liftI $ \(con, decon) -> Fn (\(Pair x y) -> return (Bool (f (decon x) (decon y))))
    liftBBB :: (Bool -> Bool -> Bool) -> Value
    liftBBB f = Fn (\(Pair (Bool a) (Bool b)) -> pure (Bool (f a b)))

mono :: String -> Annotated Type
mono s = runInternal (kEnv .= initialKEnv >> parse s :: Praxis (Annotated Type))

poly :: String -> Annotated QType
poly s = runInternal (kEnv .= initialKEnv >> parse s :: Praxis (Annotated QType))

runWithPrelude :: Praxis a -> IO (Either String a)
runWithPrelude c = runPraxis (importPrelude >> c) where
  importPrelude :: Praxis ()
  importPrelude = do
    kEnv .= initialKEnv
    iEnv .= initialIEnv
    inbuilts <- mapM (\(n, t, v) -> (\n -> (n, t, v)) <$> Rename.intro n) inbuilts
    let initialTEnv = Env.Linear.fromList $ map (\(n, t, _) -> (n, t)) inbuilts
    tEnv .= initialTEnv
    let initialVEnv = Env.Lazy.fromList $ map (\(n, _, v) -> (n, v)) inbuilts
    vEnv .= initialVEnv
    flags . silent .= True
    parse prelude :: Praxis (Annotated Program)
    flags . silent .= False


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
