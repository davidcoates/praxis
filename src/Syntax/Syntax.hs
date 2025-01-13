{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}

module Syntax.Syntax
  ( Syntax(..)
  , SyntaxT(..)
  , _Cons
  , _Nil
  , _Just
  , _Nothing
  , _Left
  , _Right
  , many
  , atLeast
  , some
  , optional
  , prefix
  , prefix'
  , swap
  ) where

import           Common
import           Introspect
import           Stage
import           Syntax.Prism
import           Syntax.TH
import           Term
import           Token

import           GHC.Exts     (Constraint)
import           Prelude      hiding (maybe, pure, (*>), (<$>), (<*), (<*>))

infixr 4 <$>
infixr 4 <*>
infixr 4 *>
infixr 4 <*
infixl 3 <|>

-- | Syntax abstracts over Parsers and Unparsers (pretty printers).
-- It uses "Prisms" to extend parser combinators (applicative, alternative) to be contravariant as well as covariant.
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
  expected :: String -> f a
  internal :: f a -> f a -- for internal constructs, supports printing but not parsing

class (IsStage s, Syntax f) => SyntaxT f s where
  annotated :: IsTerm a => f (a s) -> f (Annotated s a)
  blank :: IsTerm a => StageT s -> TermT a -> f (Annotation s a)


_Cons :: Prism [a] (a, [a])
_Cons = Prism (\(x, xs) -> x:xs) (\case { [] -> Nothing; x:xs -> Just (x, xs)})

_Nil :: Prism [a] ()
_Nil = Prism (const []) (\case { [] -> Just (); _ -> Nothing })

definePrisms ''Maybe

many :: Syntax f => f a -> f [a]
many p = _Cons <$> p <*> many p <|>
         _Nil <$> pure ()

atLeast :: Syntax f => Int -> f a -> f [a]
atLeast 0 p = many p
atLeast n p = _Cons <$> p <*> atLeast (n - 1) p

some :: Syntax f => f a -> f [a]
some = atLeast 1

optional :: Syntax f => f a -> f (Maybe a)
optional p = _Just <$> p <|>
             _Nothing <$> pure ()

definePrisms ''Either

prefix :: Syntax f => f a -> (Prism d (a, b), f b) -> (Prism d (a, c), f c) -> f d
prefix a (l, b) (r, c) = Prism f g <$> a <*> (_Left <$> b <|> _Right <$> c) where
  f (a, Left b)  = construct l (a, b)
  f (a, Right c) = construct r (a, c)
  g d = case (destruct l d, destruct r d) of
    (Just (a, x), Nothing) -> Just (a, Left x)
    (Nothing, Just (a, x)) -> Just (a, Right x)
    (Nothing, Nothing)     -> Nothing

prefix' :: Syntax f => f a -> (Prism d (a, b), f b) -> Prism d a -> f d
prefix' a (l, b) r = Prism f g <$> a <*> (_Just <$> b <|> _Nothing <$> pure ()) where
  f (a, Just b)  = construct l (a, b)
  f (a, Nothing) = construct r a
  g d = case (destruct l d, destruct r d) of
    (Just (a, b), Nothing) -> Just (a, Just b)
    (Nothing, Just a)      -> Just (a, Nothing)
    (Nothing, Nothing)     -> Nothing

swap :: Prism (a, b) (b, a)
swap = Prism (\(a, b) -> (b, a)) (\(a, b) -> Just (b, a))
