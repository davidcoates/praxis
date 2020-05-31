{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Syntax.Syntax
  ( Syntax(..)
  , cons
  , nil
  , maybe
  , nothing
  , many
  , atLeast
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
  annotated :: Term a => f a -> f (Annotated a)
  combine :: f Void -> ((Annotated a, Annotated a) -> a) -> (Annotated a, Annotated a) -> Annotated a -- FIXME this is a hack

cons :: Prism [a] (a, [a])
cons = Prism (\(x, xs) -> x:xs) (\case { [] -> Nothing; x:xs -> Just (x, xs)})

nil :: Prism [a] ()
nil = Prism (const []) (\case { [] -> Just (); _ -> Nothing })

-- FIXME call this just?!?! definePrisms ''Maybe ?!
maybe :: Prism (Maybe a) a
maybe = Prism Just id

nothing :: Prism (Maybe a) ()
nothing = Prism (const Nothing) (\case { Nothing -> Just (); _ -> Nothing })

many :: Syntax f => f a -> f [a]
many p = cons <$> p <*> many p <|>
         nil <$> pure ()

atLeast :: Syntax f => Int -> f a -> f [a]
atLeast 0 p = many p
atLeast n p = cons <$> p <*> atLeast (n - 1) p

some :: Syntax f => f a -> f [a]
some = atLeast 1

optional :: Syntax f => f a -> f (Maybe a)
optional p = maybe <$> p <|>
             nothing <$> pure ()
