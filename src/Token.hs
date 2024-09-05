{-# LANGUAGE FlexibleInstances #-}

module Token
  ( Token(..)
  ) where

import           Common
import qualified Data.Monoid.Colorful as Color
import           Term                 (Lit (..))

data Token = Annotation (Printable String)
           | ConId Name
           | Layout Char
           | Lit Lit
           | ReservedCon Name
           | ReservedSym Name
           | ReservedId Name
           | Special Char
           | Uni Name -- ^ A unification variable
           | VarId Name
           | VarSym Name
  deriving Eq

unstyle :: Colored a -> Colored a
unstyle x = case x of
  Nil            -> Nil
  Value x        -> Value x
  Style _ x      -> unstyle x
  Fg c x         -> Fg c (unstyle x)
  Bg c x         -> Bg c (unstyle x)
  Color.Pair x y -> Color.Pair (unstyle x) (unstyle y)

highlight = RGB 216 213 199

instance Pretty Token where
  pretty (Annotation (Printable p)) = Printable (\opt -> let s = p opt in if null s then Nil else Fg Black (Bg highlight (Value "[" <> unstyle s <> Value "]")))
  pretty x = pretty $ case x of
    ConId s       -> Value $ s
    Layout c      -> Fg DullRed $ Value [c]
    Lit l         -> Fg Blue $ Value $ show l
    ReservedCon s -> Value s
    ReservedSym s -> Fg Green $ Value s
    ReservedId s  -> Style Bold $ Value s
    Special c     -> Fg Black $ Value [c]
    Uni s         -> Fg Magenta $ Value s
    VarId s       -> Value $ s
    VarSym s      -> Value $ s

instance Pretty (Sourced Token) where
  pretty (_ :< x) = pretty x
