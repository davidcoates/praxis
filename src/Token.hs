{-# LANGUAGE FlexibleInstances #-}

module Token
  ( Token(..)
  ) where

import           Common
import qualified Data.Monoid.Colorful as Colored
import           Term                 (Lit (..))


data Token
  = Annotation (Colored String)
  | ConId Name
  | Layout Char
  | Lit Lit
  | ReservedCon Name
  | ReservedSym Name
  | ReservedId Name
  | Special Char
  | Uni Token
  | VarId Name
  | VarIdRef Name
  | VarIdValue Name
  | VarIdView Name
  | VarSym Name
  deriving Eq

unstyle :: Colored a -> Colored a
unstyle x = case x of
  Colored.Nil       -> Colored.Nil
  Colored.Value x   -> Colored.Value x
  Colored.Style _ x -> unstyle x
  Colored.Fg c x    -> Colored.Fg c (unstyle x)
  Colored.Bg c x    -> Colored.Bg c (unstyle x)
  Colored.Pair x y  -> Colored.Pair (unstyle x) (unstyle y)

highlight = RGB 216 213 199

instance Pretty Token where
  pretty (Annotation str) =
    if null str
      then Colored.Nil
      else Colored.Fg Black (Colored.Bg highlight ("[" <> unstyle str <> "]"))
  pretty (Uni t) =
    let str = pretty t in
      if null str
        then Colored.Nil
        else Colored.Style Underline (unstyle str)
  pretty x = pretty $ case x of
    ConId s       -> Colored.Value $ s
    Layout c      -> Colored.Fg Red $ Colored.Value [c]
    Lit l         -> Colored.Fg Blue $ Colored.Value $ show l
    ReservedCon s -> Colored.Value s
    ReservedSym s -> Colored.Fg Green $ Colored.Value s
    ReservedId s  -> Colored.Style Bold $ Colored.Value s
    Special c     -> Colored.Fg Black $ Colored.Value [c]
    VarId s       -> Colored.Value $ s
    VarIdRef s    -> Colored.Fg Yellow $ Colored.Value ('&':s)
    VarIdValue s  -> Colored.Fg Cyan $ Colored.Value  ('!':s)
    VarIdView s   -> Colored.Fg Magenta $ Colored.Value ('?':s)
    VarSym s      -> Colored.Value $ s

instance Pretty (Sourced Token) where
  pretty (_ :< x) = pretty x
