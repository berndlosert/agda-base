{-# OPTIONS --type-in-type #-}

module Data.Vector where

open import Prelude

private
  variable
    A : Set
    m n : Nat

splitAt : (m : Nat) -> Vector A (m + n) -> Vector A m * Vector A n
splitAt zero as = ([] , as)
splitAt (suc k) (a :: as) with (splitAt k as)
... | (tk , dr) = (a :: tk , dr)
