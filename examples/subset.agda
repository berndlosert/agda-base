open import Prelude

open import Data.Subset as Subset using (Subset)
open import System.IO

foo1 : Subset Nat
foo1 = Subset.fromList (1 :: 1 :: 2 :: 2 :: [])

foo2 : Subset Nat
foo2 = Subset.fromList (3 :: 3 :: 4 :: 4 :: [])

main : IO Unit
main = do
  print foo2