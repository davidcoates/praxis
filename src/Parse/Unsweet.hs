module Parse.Unsweet
  (parse, Exp(..), Lit(..), Op(..))
where

import qualified Parse.Sweet as Sweet
import Parse.Sweet (Op, Tok(..))
import Text.Parsec.Prim hiding (parse)
import Text.Parsec.Combinator
import qualified Data.Map.Strict as Map
import Data.Map (Map)
import Control.Monad (unless)
import AST

-- data Binding = Binding String Exp
 --            deriving (Show)


data InfixError = BadNeg (Op, Fixity) | BadPrec (Op, Fixity) (Op, Fixity)

instance Show InfixError where
  show (BadNeg (o, f))             = "Precedence parsing error\n" ++ indent ("cannot mix '" ++ o  ++ "' " ++ show f  ++ " and prefix '-' [infixl 6] in the same infix expression")
  show (BadPrec (o1, f1) (o2, f2)) = "Precedence parsing error\n" ++ indent ("cannot mix '" ++ o1 ++ "' " ++ show f1 ++ " and '" ++ o2 ++ "' " ++ show f2 ++ " in the same infix expression")

data Assoc = Leftfix | Rightfix | Nonfix deriving Eq

instance Show Assoc where
  show Leftfix  = "infixl"
  show Rightfix = "infixr"
  show Nonfix   = "infix"

newtype Fixity = Fixity { fixity :: (Int, Assoc) }

instance Show Fixity where
  show (Fixity (p, a)) = "[" ++ show a ++ " " ++ show p ++ "]"

opTable :: Map Op Fixity
opTable = Map.fromList [("+", Fixity (6, Leftfix)), ("==", Fixity (4, Nonfix))]

desugarExp :: Praxis Sweet.Exp -> Either ParseError (Praxis Exp)
desugarExp (_ :< Sweet.Infix ts) = resolve opTable ts
desugarExp (a :< x) = (a :<) <$> desugarExp' x 
  where desugarExp' :: PraxisTail Sweet.Exp -> Either ParseError (PraxisTail Exp)
        desugarExp' (Sweet.Lit lit)     = Right (Lit lit)
        desugarExp' (Sweet.If e1 e2 e3) = do
          [x1, x2, x3] <- mapM desugarExp [e1, e2, e3]
          return (If x1 x2 x3)

resolve :: Map Op Fixity -> [Praxis Tok] -> Either ParseError (Praxis Exp)
resolve fixityTable ts = fst <$> parseNeg ("", Fixity (-1, Nonfix)) ts
  where  
    parseNeg :: (Op, Fixity) -> [Praxis Tok] -> Either ParseError (Praxis Exp, [Praxis Tok])
    parseNeg op1 (_ :< TExp e1 : rest)
      = (\x -> parse op1 x rest) =<< desugarExp e1
    parseNeg op1 (p :< TNeg : rest)
      = do unless (prec1 < 6) (Left (newErrorMessage (indent (show (BadNeg op1))) p)) 
           (r, rest') <- parseNeg ("-", Fixity (6, Leftfix)) rest
           parse op1 (p :< Apply (p :< Prim Neg) r) rest'
      where
        (s1, Fixity (prec1, fix1)) = op1

    parse :: (Op, Fixity) -> Praxis Exp -> [Praxis Tok] -> Either ParseError (Praxis Exp, [Praxis Tok])
    parse _   e1 [] = Right (e1, [])  
    parse op1 e1 (p :< TOp s2 : rest)  
       -- case (1): check for illegal expressions  
       | prec1 == prec2 && (fix1 /= fix2 || fix1 == Nonfix)  
       = Left (newErrorMessage (indent (show (BadPrec op1 op2))) p)
 
       -- case (2): op1 and op2 should associate to the left  
       | prec1 > prec2 || (prec1 == prec2 && fix1 == Leftfix)  
       = Right (e1, p :< TOp s2 : rest)  
 
       -- case (3): op1 and op2 should associate to the right  
       | otherwise  
       = do (r, rest') <- parseNeg op2 rest  
            parse op1 (p :< Apply (p :< Apply (p :< Fun s2) e1) r) rest'
       where  
        (_, Fixity (prec1, fix1))  = op1
        op2 = (s2, fixityTable Map.! s2)
        (_, Fixity (prec2, fix2)) = op2

parse :: String -> Either ParseError (Praxis Exp)
parse s = desugarExp =<< Sweet.parse s
