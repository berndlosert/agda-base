{-# OPTIONS --type-in-type #-}

module Data.GCD where

open import Data.Bool using (if_then_else_)
open import Data.Eq using (_==_)
open import Data.Semiring using (zero; Nonzero)
open import Data.Ring using (Ring)
open import Data.Ord using (Ord; _<_)
open import Data.Type.Equality using (trustMe)

private variable A : Set

record GCD (A : Set) : Set where
  field
    overlap {{superRing}} : Ring A
    overlap {{superOrd}} : Ord A
    quot : (x y : A) -> {_ : Nonzero y} -> A
    mod : (x y : A) -> {_ : Nonzero y} -> A

open GCD {{...}} public

{-# TERMINATING #-}
gcd : {{_ : GCD A}} -> A -> A -> A
gcd m n =
  if m == zero then n
  else if n == zero then m
  else if m < n then gcd n m
  else gcd n (mod m n {trustMe})
