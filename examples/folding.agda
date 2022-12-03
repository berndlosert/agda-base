open import Prelude

open import Data.Enum
open import Data.Foldable
open import Data.Monoid.Sum
open import System.IO

-- Elapsed (wall clock) time (h:mm:ss or m:ss): 0:05.27
-- Maximum resident set size (kbytes): 5288
test1 : Nat
test1 = sum (enumFromTo 1 100000000)

-- Elapsed (wall clock) time (h:mm:ss or m:ss): 2:37.91
-- Maximum resident set size (kbytes): 8307504
test2 : Sum Nat
test2 = foldMap asSum (enumFromTo 1 100000000)

-- Elapsed (wall clock) time (h:mm:ss or m:ss): 0:05.76
-- Maximum resident set size (kbytes): 5160
test3 : Sum Nat
test3 = mapReduce asSum (enumFromTo 1 100000000)

main : IO Unit
main = print test3