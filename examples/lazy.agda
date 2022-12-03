open import Prelude

open import Data.List as List using ()
open import Data.Stream as Stream using ()
open import System.IO

variable
  a : Set

data LazyList (a : Set) : Set where
  nil : LazyList a
  cons : a -> LazyList a -> LazyList a

take : Nat -> LazyList a -> List a
take 0 _ = []
take (suc n) nil = []
take (suc n) (cons x xs) = x :: take n xs

ones : LazyList Nat
ones = cons 1 (ones)

ones' : List Nat
ones' = (1 ::_) $! ones'

main : IO Unit
main = do
  print $ Stream.take 5 (pure (id {Nat} 9))