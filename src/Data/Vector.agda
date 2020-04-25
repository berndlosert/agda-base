{-# OPTIONS --type-in-type #-}

module Data.Vector where

open import Prelude

private
  variable
    A : Set
    m n : Nat

data Vector (A : Set) : Nat -> Set where
  [] : Vector A zero
  _::_ : ∀ {n} -> A -> Vector A n -> Vector A (suc n)

instance
  appendVector : ∀ {m n A}
    -> Append (Vector A m) (Vector A n) (Vector A (m + n))
  appendVector ._++_ [] ys = ys
  appendVector ._++_ (x :: xs) ys = x :: xs ++ ys

splitAt : (m : Nat) -> Vector A (m + n) -> Vector A m * Vector A n
splitAt zero as = ([] , as)
splitAt (suc k) (a :: as) with (splitAt k as)
... | (tk , dr) = (a :: tk , dr)
