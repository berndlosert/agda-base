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
