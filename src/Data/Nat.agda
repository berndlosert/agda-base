{-# OPTIONS --type-in-type #-}

module Data.Nat where

open import Prelude

-- Determine if a natural number is even or odd.
even odd : Nat -> Bool
even n = n % 2 == 0
odd n = not (even n)

-- The greatest common divisor of two natural numbers.
{-# TERMINATING #-}
gcd : Nat -> Nat -> Nat
gcd m 0 = m
gcd 0 n = n
gcd m n@(suc _) = if m > n then gcd n (m % n) else gcd n m

{-# COMPILE GHC gcd = Prelude.gcd #-}
