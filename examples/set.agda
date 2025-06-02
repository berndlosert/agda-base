open import Prelude

open import Data.Set as Set using (Set)
open import System.IO

foo1 : Set Nat
foo1 = Set.fromList (1 :: 1 :: 2 :: 2 :: [])

foo2 : Set Nat
foo2 = Set.fromList (3 :: 3 :: 4 :: 4 :: [])

main : IO Unit
main = do
  print foo2