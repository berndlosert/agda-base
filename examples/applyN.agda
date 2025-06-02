open import Prelude

open import Data.Monoid.Sum
open import System.IO

instance
    _ = FromNat-Nat1

-- Maximum resident set size (kbytes): 6483656
-- Elapsed (wall clock) time (h:mm:ss or m:ss): 0:16.10
n : Nat
n = applyN 100_000_000 (_+ 1) 0

-- Maximum resident set size (kbytes): 11484
-- Elapsed (wall clock) time (h:mm:ss or m:ss): 0:01.22
n' : Nat
n' = applyN' 100_000_000 (_+ 1) 0

-- Maximum resident set size (kbytes): 8128528
-- Elapsed (wall clock) time (h:mm:ss or m:ss): 0:16.97
m : Sum Nat1
m = stimes 100_000_000 (asSum 1)

-- Maximum resident set size (kbytes): 12024
-- Elapsed (wall clock) time (h:mm:ss or m:ss): 0:01.55
m' : Sum Nat1
m' = stimes' 100_000_000 (asSum 1)

-- Maximum resident set size (kbytes): 8114992
-- Elapsed (wall clock) time (h:mm:ss or m:ss): 0:19.27
k : Sum Nat
k = mtimes 100_000_000 (asSum 1)

-- Maximum resident set size (kbytes): 11732
-- Elapsed (wall clock) time (h:mm:ss or m:ss): 0:01.35
k' : Sum Nat
k' = mtimes' 100_000_000 (asSum 1)

main : IO Unit
main = print k'
