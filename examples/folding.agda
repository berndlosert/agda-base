open import Prelude

open import Control.Lens
open import Data.Enum
open import Data.Monoid.Sum
open import Data.Monoid.Dual
open import Data.Monoid.Endo
open import Data.Monoid.Foldable
open import Data.Semigroup.Foldable
open import System.IO

variable
  a b : Type
  t : Type -> Type

instance
  _ = FromNat-Int

-- Elapsed (wall clock) time (h:mm:ss or m:ss): 0:11.33
-- Maximum resident set size (kbytes): 5212
test1 : Int
test1 = sum (enumFromTo 1 100_000_000)

-- Elapsed (wall clock) time (h:mm:ss or m:ss): 2:32.49
-- Maximum resident set size (kbytes): 8332300
test2 : Sum Int
test2 = foldMap asSum (enumFromTo 1 100_000_000)

-- Elapsed (wall clock) time (h:mm:ss or m:ss): 0:13.03
-- Maximum resident set size (kbytes): 5044
test3 : Sum Int
test3 = foldMap' asSum (enumFromTo 1 100_000_000)

-- Elapsed (wall clock) time (h:mm:ss or m:ss): 0:14.89
-- Maximum resident set size (kbytes): 4788
test4 : Sum Int
test4 = (fold' <<< map asSum) (enumFromTo 1 100_000_000)

-- Elapsed (wall clock) time (h:mm:ss or m:ss): 0:18.62
-- Maximum resident set size (kbytes): 5032
test5 : Int
test5 = foldlOf' each _+_ 0 (enumFromTo 1 100_000_000)

-- Elapsed (wall clock) time (h:mm:ss or m:ss): 0:12.15
-- Maximum resident set size (kbytes): 4960
test6 : Int
test6 = foldl' _+_ 0 (enumFromTo 1 100_000_000)

-- Elapsed (wall clock) time (h:mm:ss or m:ss): 0:15.89
-- Maximum resident set size (kbytes): 5168
test7 : Sum Int
test7 = foldMap1' asSum (1 :: enumFromTo 2 100_000_000)

-- Elapsed (wall clock) time (h:mm:ss or m:ss): 2:50.80
-- Maximum resident set size (kbytes): 8305792
test8 : Sum Int
test8 = foldMap1 asSum (1 :: enumFromTo 2 100_000_000)

-- Elapsed (wall clock) time (h:mm:ss or m:ss): 0:16.70
-- Maximum resident set size (kbytes): 4968
test9 : Int
test9 = sumOf each (enumFromTo 1 100_000_000)

main : IO Unit
main = print test9