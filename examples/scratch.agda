open import Prelude

open import Data.Enum
open import System.IO

foo1 : List Nat
foo1 = enumFromTo 3 14

foo2 : List Nat
foo2 = enumFromTo 17 5

foo3 : List Int
foo3 = enumFromTo -13 7

foo4 : List Int
foo4 = enumFromTo 8 29

main : IO Unit
main = do
  print foo1
  print foo2
  print foo3
  print foo4
