open import Prelude

open import Data.List as List using ()
open import System.IO
open import Test.QC

propRevUnit : Nat -> Bool
propRevUnit x = List.reverse (x :: []) == x :: []

propRevApp : List Nat -> List Nat -> Bool
propRevApp xs ys = List.reverse (xs <> ys) == List.reverse xs <> List.reverse ys

main : IO Unit
main = quickCheck propRevApp