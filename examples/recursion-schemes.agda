open import Prelude

open import Data.Functor.Recursive
open import System.IO

mySum : List Nat -> Nat
mySum = cata \ where
 [] -> 0
 (x :: sumXs) -> x + sumXs

main : IO Unit
main = do
  print $ project (the Nat 1 :: 2 :: 3 :: [])
  print $ mySum (10 :: 11 :: 12 :: [])