open import Prelude

open import Data.List as List using ()
open import Data.Stream as Stream using ()
open import System.IO

variable
  a : Type

data LazyList (a : Type) : Type where
  nil : LazyList a
  cons : a -> LazyList a -> LazyList a

take : Nat -> LazyList a -> List a
take 0 _ = []
take (suc n) nil = []
take (suc n) (cons x xs) = x :: take n xs

lazyones : LazyList Nat
lazyones = cons 1 (lazyones)

ones : List Nat
ones = (1 ::_) $! ones

main : IO Unit
main = do
  print (Stream.take 5 (pure 9))