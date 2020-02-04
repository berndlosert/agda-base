{-# OPTIONS --type-in-type #-}

module Data.Nat where

open import Data.Nat.Base public
  hiding (module Nat)

module Nat where

  -- Determine if a natural number is even or odd.

  open import Data.Bool

  even : Nat -> Bool
  even n = n % 2 == 0

  odd : Nat -> Bool
  odd n = not (even n)

  -- The greatest common divisor of two natural numbers.

  {-# TERMINATING #-}
  gcd : Nat -> Nat -> Nat
  gcd m 0 = m
  gcd 0 n = n
  gcd m n@(suc _) = if m > n then gcd n (m % n) else gcd n m
  {-# COMPILE GHC gcd = Prelude.gcd #-}
