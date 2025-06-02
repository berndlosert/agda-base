open import Prelude

open import Control.Lens
open import Control.Reduce
open import Data.Enum
open import Data.List as List using ()
open import Data.List.Nonempty
open import Data.Monoid.Dual
open import Data.Monoid.Endo
open import Data.Monoid.Foldable
open import Data.Monoid.Sum
open import Data.Semigroup.Foldable
open import System.IO

variable
  a b : Type
  t : Type -> Type

instance
  _ = FromNat-Int

test1 : Int
test1 = sum (enumFromTo 1 100_000_000)

test2 : Sum Int
test2 = foldMap asSum (enumFromTo 1 100_000_000)

test4 : Sum Int
test4 = (fold <<< map asSum) (enumFromTo 1 100_000_000)

test5 : Int
test5 = foldlOf each _+_ 0 (enumFromTo 1 100_000_000)

test6 : Int
test6 = foldl _+_ 0 (enumFromTo 1 100_000_000)

test8 : Sum Int
test8 = foldMap1 asSum (1 :: enumFromTo 2 100_000_000)

test9 : Int
test9 = sumOf each (enumFromTo 1 100_000_000)

test10 : Int
test10 = foldl1 _+_ id (1 :: enumFromTo 2 100_000_000)

test11 : Nat
test11 = length {List} {Int} (1 :: enumFromTo 2 100_000_000)

test12 : Nat
test12 = reduce intoSum (enumFromTo 1 100_000_000)

test13 : Int
test13 = sum $ toList {List1} {Int} (1 :: enumFromTo 2 100_000_000)

test14 : IO Unit
test14 = foldlM (\ tt x -> print x) tt (enumFromTo {Nat} 1 5)

test15 : IO Unit
test15 = foldrM1 (\ x tt -> print x) print (1 :: enumFromTo {Nat} 2 5)

main : IO Unit
main = test15