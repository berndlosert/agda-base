open import Prelude

open import Data.Foldable
open import Data.List.Elem
open import Data.Either.Nary
open import System.IO

variable
  a : Set

x : foldr Either Void (Nat :: String :: Bool :: [])
x = right (right (left true))

u : EitherN (Nat :: String :: Bool :: [])
u = inject Elem2 false

v : EitherN (String :: Bool :: String :: [])
v = inject Elem2 "foo"

w : EitherN (Nat :: String :: Bool :: [])
w = relax (consSub Elem1 $ consSub Elem2 $ consSub Elem1 nilSub) v

n : Nat
n = (eitherN onNat $ eitherN onString $ eitherN onBool $ absurd) u
  where
    onNat : Nat -> Nat
    onNat n = n + 1

    onString : String -> Nat
    onString _ = 1

    onBool : Bool -> Nat
    onBool _ = 2

main : IO Unit
main = do
  print (project Elem0 u)
  print (project Elem2 u)
  print (project Elem2 v)
  print (project Elem0 w)