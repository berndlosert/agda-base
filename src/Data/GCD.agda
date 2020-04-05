{-# OPTIONS --type-in-type #-}

module Data.GCD where

open import Data.Bool using (if_then_else_)
open import Data.Eq using (_==_)
open import Data.Semiring using (zero; Nonzero; toNonzero)
open import Data.Ring using (Ring)
open import Data.Ord using (Ord; _<_)
open import Data.Type.Equality using (trustMe)

private variable A : Set

record Division (A : Set) : Set where
  infixr 7 _/_ _%_
  field
    overlap {{superRing}} : Ring A
    IsNonZero : A -> Set
    _/_ : (x y : A) -> {_ : IsNonzero y} -> A
    _%_ : (x y : A) -> {_ : IsNonzero y} -> A

open Division {{...}} public
