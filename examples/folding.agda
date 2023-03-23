open import Prelude

open import Data.Enum
open import Data.Foldable
open import Data.Monoid.Sum
open import System.IO

variable
  a b : Set
  t : Set -> Set

-- Elapsed (wall clock) time (h:mm:ss or m:ss): 0:05.27
-- Maximum resident set size (kbytes): 5288
test1 : Nat
test1 = sum (enumFromTo 1 100_000_000)

-- Elapsed (wall clock) time (h:mm:ss or m:ss): 2:37.91
-- Maximum resident set size (kbytes): 8307504
test2 : Sum Nat
test2 = foldMap asSum (enumFromTo 1 100_000_000)

-- Elapsed (wall clock) time (h:mm:ss or m:ss): 0:05.76
-- Maximum resident set size (kbytes): 5160
test3 : Sum Nat
test3 = foldMap' asSum (enumFromTo 1 100_000_000)

-- Elapsed (wall clock) time (h:mm:ss or m:ss): 0:10.38
-- Maximum resident set size (kbytes): 5268
test4 : Sum Int
test4 = foldMap' asSum (enumFromTo 1 100_000_000)

-- Elapsed (wall clock) time (h:mm:ss or m:ss): 0:10.58
-- Maximum resident set size (kbytes): 5100
test5 : Int
test5 = sum (enumFromTo 1 100_000_000)

main : IO Unit
main = print test2