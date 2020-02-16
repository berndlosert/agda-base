{-# OPTIONS --type-in-type #-}

module Data.Vec where

open import Data.Vec.Base public
  hiding (module Vec)

module Vec where

  -- Split a vector into two parts.

  open import Data.Pair public

  splitAt : forall m {n X} -> Vec X (m + n) -> Vec X m * Vec X n
  splitAt zero xs = Pair: [] xs
  splitAt (suc k) (x :: xs) with (splitAt k xs)
  ... | (Pair: tk dr) = Pair: (x :: tk) dr
