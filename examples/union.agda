open import Prelude

open import Data.List.Elem
open import Data.Union
open import System.IO

u : Union (Nat :: String :: Bool :: [])
u = inject false

v : Union (String :: String :: String :: [])
v = inject {{Elem2}} "foo"

n : Nat
n = (union onNat $ union onString $ union onBool $ absurd) u
  where
    onNat : Nat -> Nat
    onNat n = n + 1

    onString : String -> Nat
    onString _ = 1

    onBool : Bool -> Nat
    onBool _ = 2

main : IO Unit
main = print (project {{Elem2}} v)