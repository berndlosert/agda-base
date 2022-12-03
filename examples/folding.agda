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

-- Elapsed (wall clock) time (h:mm:ss or m:ss): 2:33.65
-- Maximum resident set size (kbytes): 8266472
test3 : Sum Nat
test3 = fold $ coerce {List Nat} {List (Sum Nat)} (enumFromTo 1 100000000)

-- Elapsed (wall clock) time (h:mm:ss or m:ss): 0:07.76
-- Maximum resident set size (kbytes): 5128
test4 : Sum Nat
test4 = foldl (coerce (the (Nat -> Nat -> Nat) _+_)) (asSum 0) $ coerce {List Nat} {List (Sum Nat)} (enumFromTo 1 100000000)

-- Elapsed (wall clock) time (h:mm:ss or m:ss): 0:08.74
-- Maximum resident set size (kbytes): 5032
test5 : Sum Nat
test5 = foldl _<>_ (asSum 0) $ coerce {List Nat} {List (Sum Nat)} (enumFromTo 1 100000000)

main : IO Unit
main = print test5