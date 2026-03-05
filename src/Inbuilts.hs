{-# LANGUAGE QuasiQuotes #-}

module Inbuilts
  ( runWithPrelude
  , integral
  , clone
  , dispose
  , copy
  , capture
  ) where

import           Check.State
import           Common
import           Eval.State
import           Eval.Value                (Value (..), integerToValue,
                                            valueToInteger)
import qualified Eval.Value                as Value
import           Introspect
import qualified Parse                     (run)
-- import qualified Check.Kind.Check          as Check.Kind (run)
-- import qualified Check                     as Check (run)
import           Praxis
import           Stage
import           Term                      hiding (Lit (..), Pair, Unit)

import           Control.Monad.Trans.Class (MonadTrans (..))
import qualified Control.Monad.Trans.State as State (get)
import qualified Data.Map                  as Map
import qualified Data.Map.Lazy             as Map.Lazy
import qualified Data.Set                  as Set
import           System.IO.Unsafe          (unsafePerformIO)
import           Text.RawString.QQ


runInternal :: Praxis a -> a
runInternal c = case unsafePerformIO (runPraxis (flags . silent .= True >> c)) of
  Left e  -> error ("internal computation failed: " ++ e)
  Right x -> x

kind :: String -> Annotated KindCheck Kind
kind s = cast $ runInternal (Parse.run s) where
  cast :: forall a. IsTerm a => Annotated Parse a -> Annotated KindCheck a
  cast ((src, _) :< term) = case termT :: TermT a of
    KindT -> (src, ()) :< runIdentity (recurseTerm (Identity . cast) term)

initialTypeConEnv :: TypeConEnv
initialTypeConEnv = Map.fromList
  [
  -- Types
    (mkName "Array",    kind "Type -> Type")
  , (mkName "Bool",     kind "Type")
  , (mkName "Char",     kind "Type")
  , (mkName "Fn",       kind "Type -> Type -> Type")
  , (mkName "I8",       kind "Type")
  , (mkName "I16",      kind "Type")
  , (mkName "I32",      kind "Type")
  , (mkName "I64",      kind "Type")
  , (mkName "ISize",    kind "Type")
  , (mkName "Ref",      kind "Type -> Type")
  , (mkName "String",   kind "Type")
  , (mkName "U8",       kind "Type")
  , (mkName "U16",      kind "Type")
  , (mkName "U32",      kind "Type")
  , (mkName "U64",      kind "Type")
  , (mkName "USize",    kind "Type")
  , (mkName "Unit",     kind "Type")
  , (mkName "Pair",     kind "Type -> Type -> Type")
  -- Constraints
  , (mkName "Clone",    kind "Type -> Constraint")
  , (mkName "Dispose",  kind "Type -> Constraint")
  , (mkName "Copy",     kind "Type -> Constraint")
  , (mkName "Capture",  kind "Type -> Constraint")
  , (mkName "Integral", kind "Type -> Constraint")
  ]


-- TODO should be replaced with instances in prelude

integral :: Annotated TypeCheck Type -> Annotated TypeCheck TypeConstraint
integral t = phantom (TypeIsInstance (phantom (TypeApply (phantom (TypeCon (mkName "Integral"))) t)))

clone :: Annotated TypeCheck Type -> Annotated TypeCheck TypeConstraint
clone t = phantom (TypeIsInstance (phantom (TypeApply (phantom (TypeCon (mkName "Clone"))) t)))

dispose :: Annotated TypeCheck Type -> Annotated TypeCheck TypeConstraint
dispose t = phantom (TypeIsInstance (phantom (TypeApply (phantom (TypeCon (mkName "Dispose"))) t)))

copy :: Annotated TypeCheck Type -> Annotated TypeCheck TypeConstraint
copy t = phantom (TypeIsInstance (phantom (TypeApply (phantom (TypeCon (mkName "Copy"))) t)))

capture :: Annotated TypeCheck Type -> Annotated TypeCheck TypeConstraint
capture t = phantom (TypeIsInstance (phantom (TypeApply (phantom (TypeCon (mkName "Capture"))) t)))

initialInstanceEnv :: InstanceEnv
initialInstanceEnv = Map.fromList
  [ (mkName "Array", Map.fromList
    [ (mkName "Clone",   \[t] -> (Inbuilt, IsInstanceOnlyIf [clone t]))
    , (mkName "Dispose", \[t] -> (Inbuilt, IsInstanceOnlyIf [dispose t]))
    ]
    )
  , (mkName "Bool", primitive)
  , (mkName "Char", primitive)
  , (mkName "Fn", Map.fromList
    [ (mkName "Clone",   \_ -> (Inbuilt, IsInstance))
    , (mkName "Dispose", \_ -> (Inbuilt, IsInstance))
    , (mkName "Copy",    \_ -> (Inbuilt, IsInstance))
    , (mkName "Capture", \_ -> (Inbuilt, IsInstance))
    ]
    )
  , (mkName "I8",    integralInst)
  , (mkName "I16",   integralInst)
  , (mkName "I32",   integralInst)
  , (mkName "I64",   integralInst)
  , (mkName "ISize", integralInst)
  , (mkName "Pair", Map.fromList
    [ (mkName "Clone",   \[a, b] -> (Trivial, IsInstanceOnlyIf [clone a, clone b]))
    , (mkName "Dispose", \[a, b] -> (Trivial, IsInstanceOnlyIf [dispose a, dispose b]))
    , (mkName "Copy",    \[a, b] -> (Trivial, IsInstanceOnlyIf [copy a, copy b]))
    , (mkName "Capture", \[a, b] -> (Trivial, IsInstanceOnlyIf [capture a, capture b]))
    ]
    )
  , (mkName "Ref", Map.fromList
    [ (mkName "Clone",   \_ -> (Trivial, IsInstance))
    , (mkName "Dispose", \_ -> (Trivial, IsInstance))
    , (mkName "Copy",    \_ -> (Trivial, IsInstance))
    ]
    )
  , (mkName "String", Map.fromList
    [ (mkName "Clone",   \_ -> (Inbuilt, IsInstance))
    , (mkName "Dispose", \_ -> (Inbuilt, IsInstance))
    ]
    )
  , (mkName "U8",    integralInst)
  , (mkName "U16",   integralInst)
  , (mkName "U32",   integralInst)
  , (mkName "U64",   integralInst)
  , (mkName "USize", integralInst)
  , (mkName "Unit", primitive)
  ] where
    primitive = Map.fromList
      [ (mkName "Clone",   \_ -> (Trivial, IsInstance))
      , (mkName "Dispose", \_ -> (Trivial, IsInstance))
      , (mkName "Copy",    \_ -> (Trivial, IsInstance))
      , (mkName "Capture", \_ -> (Trivial, IsInstance))
      ]
    integralInst = primitive `Map.union` Map.fromList
      [ (mkName "Integral", \_ -> (Inbuilt, IsInstance))
      ]


-- FIXME: Intiailize "scopes"

inbuilts :: [(Name, Annotated TypeCheck QType, Value)]
inbuilts =
  [ (mkName "add"
    , poly "forall a | Integral a. (a, a) -> a" -- TODO should be Num, not Integral
    , liftIII (+)
    )
  , (mkName "subtract"
    , poly "forall a | Integral a. (a, a) -> a"
    , liftIII (-)
    )
  , (mkName "multiply"
    , poly "forall a | Integral a. (a, a) -> a"
    , liftIII (*)
    )
  , (mkName "negate"
    , poly "forall a | Integral a. a -> a"
    , liftI $ \(con, decon) -> Fn (\x -> return (con (negate (decon x))))
    )
  , (mkName "get_int"
    , poly "forall a | Integral a. () -> a"
    , liftI $ \(con, decon) -> Fn (\Unit -> liftIOUnsafe (con <$> readLn))
    )
  , (mkName "get_str"
    , poly "() -> String"
    , Fn (\Unit -> Value.String <$> liftIOUnsafe getContents) -- TODO need to make many of these functions strict?
    )
  , (mkName "put_int"
    , poly "forall a | Integral a. a -> ()"
    , liftI $ \(_, decon) -> Fn (\i -> liftIOUnsafe (print (decon i) >> pure Unit))
    )
  , (mkName "put_str"
    , poly "forall &r. &r String -> ()"
    , Fn (\(String s) -> liftIOUnsafe (putStr s) >> pure Unit)
    )
  , (mkName "put_str_ln"
    , poly "forall &r. &r String -> ()"
    , Fn (\(String s) -> liftIOUnsafe (putStrLn s) >> pure Unit)
    )
  , (mkName "compose"
    , poly "forall a b c. (b -> c, a -> b) -> a -> c"
    , Fn (\(Pair (Fn f) (Fn g)) -> pure (Fn (\x -> g x >>= f)))
    )
  , (mkName "print"
    , poly "forall &r a. &r a -> ()" -- TODO should have Show constraint
    , Fn (\x -> liftIOUnsafe (print x >> pure Unit))
    )
  , (mkName "new_array"
    , poly "forall a. (USize, () -> a) -> Array a"
    , Fn (\(Pair (USize i) v) -> Value.newArray i v)
    )
  , (mkName "at_array"
    , poly "forall &r a. (&r Array a, USize) -> &r a"
    , Fn (\(Pair (Array a) (USize i)) -> Value.readArray a i)
    )
  , (mkName "len_array"
    , poly "forall &r a. &r Array a -> USize"
    , Fn (\(Array a) -> USize <$> Value.lenArray a)
    )
  , (mkName "set_array"
    , poly "forall a. (Array a, USize, a) -> Array a"
    , Fn (\(Pair (Array a) (Pair (USize i) e)) -> Value.writeArray a i e >> pure (Array a))
    )
  , (mkName "not"
    , poly "Bool -> Bool"
    , Fn (\(Bool a) -> pure (Bool (not a)))
    )
  , (mkName "or"
    , poly "(Bool, Bool) -> Bool"
    , liftBBB (||)
    )
  , (mkName "and"
    , poly "(Bool, Bool) -> Bool"
    , liftBBB (&&)
    )
  , (mkName "eq"
    , poly "forall a | Integral a. (a, a) -> Bool" -- TODO should be Eq, not Integral
    , liftIIB (==)
    )
  , (mkName "neq"
    , poly "forall a | Integral a. (a, a) -> Bool"
    , liftIIB (/=)
    )
  , (mkName "lt"
    , poly "forall a | Integral a. (a, a) -> Bool" -- TODO should be Ord, not Integral
    , liftIIB (<)
    )
  , (mkName "gt"
    , poly "forall a | Integral a. (a, a) -> Bool"
    , liftIIB (>)
    )
  , (mkName "lte"
    , poly "forall a | Integral a. (a, a) -> Bool"
    , liftIIB (<=)
    )
  , (mkName "gte"
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

mono :: String -> Annotated TypeCheck Type
mono s = cast $ runInternal (checkState . kindState . typeConEnv .= initialTypeConEnv >> Parse.run s) where
  cast :: forall a. IsTerm a => Annotated Parse a -> Annotated TypeCheck a
  cast ((src, _) :< term) = case termT :: TermT a of
    TypeT -> (src, ()) :< runIdentity (recurseTerm (Identity . cast) term)

poly :: String -> Annotated TypeCheck QType
poly s = cast $ runInternal (checkState . kindState . typeConEnv .= initialTypeConEnv >> Parse.run s) where
  cast :: forall a. IsTerm a => Annotated Parse a -> Annotated TypeCheck a
  cast ((src, _) :< term) = case termT :: TermT a of
    TypeT           -> (src, ()) :< runIdentity (recurseTerm (Identity . cast) term)
    QTypeT          -> (src, ()) :< runIdentity (recurseTerm (Identity . cast) term)
    TypePatT        -> (src, ()) :< runIdentity (recurseTerm (Identity . cast) term)
    TypeConstraintT -> (src, ()) :< runIdentity (recurseTerm (Identity . cast) term)

runWithPrelude :: Praxis a -> IO (Either String a)
runWithPrelude c = runPraxis (importPrelude >> c) where
  importPrelude :: Praxis ()
  importPrelude = do
    checkState . instanceEnv .= initialInstanceEnv
    checkState . kindState . typeConEnv .= initialTypeConEnv
    let initialVarEnv = Map.fromList $ map (\(n, qTy, _) -> (n, (mempty :: Usage, qTy))) inbuilts
    checkState . typeState . varEnv .= initialVarEnv
    let initialValueEnv = Map.Lazy.fromList $ map (\(n, _, v) -> (n, v)) inbuilts
    evalState . valueEnv .= initialValueEnv
    flags . silent .= True
    Parse.run prelude :: Praxis (Annotated Parse Program)
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
