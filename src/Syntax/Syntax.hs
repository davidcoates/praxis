{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Syntax.Syntax
  ( Syntax(..)
  , Domain(..)
  , cons
  , nil
  , maybe
  , nothing
  , many
  , some
  , optional
  ) where

import           Common
import           Introspect
import           Syntax.Prism
import           Term
import           Token

import           GHC.Exts     (Constraint)
import           Prelude      hiding (maybe, pure, (*>), (<$>), (<*), (<*>))

infixr 4 <$>
infixr 4 <*>
infixr 4 *>
infixr 4 <*
infixl 3 <|>

class Syntax f where
  (<$>) :: Prism b a -> f a -> f b
  (<*>) :: f a -> f b -> f (a, b)
  (*>) :: f () -> f b -> f b
  (*>) a b = Prism snd (\b -> Just ((), b)) <$> a <*> b
  (<*) :: f a -> f () -> f a
  (<*) a b = Prism fst (\a -> Just (a, ())) <$> a <*> b
  empty :: f a
  (<|>) :: f a -> f a -> f a
  pure :: a -> f a
  match :: (Token -> Maybe a) -> (a -> Token) -> f a
  mark :: String -> f a
  unparseable :: f a -> f a

class Domain f s where -- TODO come up with a better name
  annotated :: Recursive a => f (a s) -> f (Annotated s a)
  combine :: f Void -> ((Annotated s a, Annotated s a) -> (a s)) -> (Annotated s a, Annotated s a) -> Annotated s a -- FIXME this is a hack

cons :: Prism [a] (a, [a])
cons = Prism (\(x, xs) -> x:xs) (\case { [] -> Nothing; x:xs -> Just (x, xs)})

nil :: Prism [a] ()
nil = Prism (const []) (\case { [] -> Just (); _ -> Nothing })

maybe :: Prism (Maybe a) a
maybe = Prism Just id

nothing :: Prism (Maybe a) ()
nothing = Prism (const Nothing) (\case { Nothing -> Just (); _ -> Nothing })

many :: Syntax f => f a -> f [a]
many p = cons <$> p <*> many p <|>
         nil <$> pure ()

some :: Syntax f => f a -> f [a]
some p = cons <$> p <*> many p

optional :: Syntax f => f a -> f (Maybe a)
optional p = maybe <$> p <|>
             nothing <$> pure ()
