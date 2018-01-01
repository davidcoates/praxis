{- 
  Parse.Unsweet converts the AST of sugared Praxis to an AST of desugared Praxis, defined in AST.hs.
  Every node of the resultant AST is annotated with source positions.
  This is where infix expressions are structured, taking in to account of local fixity declarations. (that may appear after the operator is used) 
-}

module Parse.Unsweet
  (parse)
where

import qualified Parse.Sweet as Sweet
import Parse.Sweet (Op, Tok(..))
import Text.Parsec.Combinator
import qualified Data.Map.Strict as Map
import Data.Map (Map)
import Control.Monad (unless)
import Text.Parsec.Error (showErrorMessages, errorMessages, errorPos)
import qualified Text.Parsec.Error as Parsec (ParseError)
import AST

data ParseErrorTy = SugarError Parsec.ParseError | DesugarError DesugarError

instance Show ParseErrorTy where
  show (SugarError p)   = showErrorMessages "or" "unknown parse error" "expecting" "unexpected" "end of input" (errorMessages p)
  show (DesugarError d) = "\n" ++ show d

data DesugarError = InfixError InfixError

instance Show DesugarError where
  show (InfixError e) = "precedence error when trying to structure infix expression\n" ++ indent (show e)

data InfixError = BadNeg (Op, Fixity) | BadPrec (Op, Fixity) (Op, Fixity)

instance Show InfixError where
  show (BadNeg (o, f))             = "cannot mix '" ++ o  ++ "' " ++ show f  ++ " and prefix '-' [infixl 6] in the same infix expression"
  show (BadPrec (o1, f1) (o2, f2)) = "cannot mix '" ++ o1 ++ "' " ++ show f1 ++ " and '" ++ o2 ++ "' " ++ show f2 ++ " in the same infix expression"

type ParseError = Error ParseErrorTy


-- This is the primary function, which attempts to parse a string to an annotated desugared AST
parse :: String -> Either ParseError (Praxis Exp)
parse s = case Sweet.parse s of Left p -> Left Error{ pos= SourcePos (errorPos p), stage="parsing", message = SugarError p }
                                Right e -> desugarExp e

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
        desugarExp' (Sweet.Fun s) = Right (Fun s)
        desugarExp' (Sweet.Apply x y) = do
          x' <- desugarExp x
          y' <- desugarExp y
          return (Apply x' y')

-- resolve structures infix expressions. This code was modified from https://www.haskell.org/onlinereport/haskell2010/haskellch10.html
-- Although Parsec contains functions to create infix expression Parsers, this is not sufficient for our purposes, since the desugaring is
-- complete separated from the initial parse.
resolve :: Map Op Fixity -> [Praxis Tok] -> Either ParseError (Praxis Exp)
resolve fixityTable ts = fst <$> parseNeg ("", Fixity (-1, Nonfix)) ts
  where
    parseNeg :: (Op, Fixity) -> [Praxis Tok] -> Either ParseError (Praxis Exp, [Praxis Tok])
    parseNeg op1 (_ :< TExp e1 : rest)
      = (\x -> parse op1 x rest) =<< desugarExp e1
    parseNeg op1 (p :< TNeg : rest)
      = do unless (prec1 < 6) (Left Error{pos=p, stage="desugaring", message = DesugarError (InfixError (BadNeg op1))})
           (r, rest') <- parseNeg ("-", Fixity (6, Leftfix)) rest
           parse op1 (p :< Apply (p :< Prim Neg) r) rest'
      where
        (s1, Fixity (prec1, fix1)) = op1

    parse :: (Op, Fixity) -> Praxis Exp -> [Praxis Tok] -> Either ParseError (Praxis Exp, [Praxis Tok])
    parse _   e1 [] = Right (e1, [])
    parse op1 e1 (p :< TOp s2 : rest)
       -- case (1): check for illegal expressions
       | prec1 == prec2 && (fix1 /= fix2 || fix1 == Nonfix)
       = Left Error{pos=p, stage="desugaring", message=DesugarError (InfixError (BadPrec op1 op2))}

       -- case (2): op1 and op2 should associate to the left
       | prec1 > prec2 || (prec1 == prec2 && fix1 == Leftfix)
       = Right (e1, p :< TOp s2 : rest)

       -- case (3): op1 and op2 should associate to the right
       | otherwise
       = do (r, rest') <- parseNeg op2 rest
            parse op1 (p :< Apply (p :< Apply (p :< Fun s2) e1) r) rest'
       where
        (_, Fixity (prec1, fix1))  = op1
        op2 = (s2, Map.findWithDefault (Fixity (6, Leftfix)) s2 fixityTable)
        (_, Fixity (prec2, fix2)) = op2

