{-# OPTIONS --type-in-type #-}

module Data.Vector where

open import Prelude

private
  variable
    A : Set
    m n : Nat

data Vector (A : Set) : Nat -> Set where
  [] : Vector A 0
  _::_ : ∀ {n} -> A -> Vector A n -> Vector A (suc n)

append : Vector A m -> Vector A n -> Vector A (m + n)
append [] as = as
append (a :: as) as' = a :: append as as'

splitAt : (m : Nat) -> Vector A (m + n) -> Vector A m * Vector A n
splitAt 0 as = ([] , as)
splitAt (suc k) (a :: as) with (splitAt k as)
... | (l , r) = (a :: l , r)
