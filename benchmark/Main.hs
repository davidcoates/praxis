{-# LANGUAGE QuasiQuotes #-}

module Main where

import           Util

import           Criterion
import           Criterion.Main    (defaultMain)
import           Text.RawString.QQ


program1 = trim [r|
datatype rec List a = Nil () | Cons (a, List a)

rec
  map : forall ?v a b. (?v a -> b) -> ?v List a -> List b
  map f = cases
    Nil ()       -> Nil ()
    Cons (x, xs) -> Cons (f x, (map f) xs)

rec
  sum : forall &r. &r List Int -> Int
  sum = cases
    Nil ()       -> 0
    Cons (x, xs) -> x + sum xs
|]

main :: IO  ()
main = defaultMain
  [
    bgroup "program1" [
      bench "parse"     $ nfAppIO parse program1,
      bench "check"     $ nfAppIO check program1,
      bench "translate" $ nfAppIO translate program1
    ]
  ]
