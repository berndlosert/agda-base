{-# OPTIONS --type-in-type #-}

module Data.Ord where

-- This is used by the compare operation in Ord.
data Ordering : Set where
  LT EQ GT : Ordering

instance
  -- Ordering is a semigroup.
  open import Data.Semigroup
  Semigroup:Ordering : Semigroup Ordering
  Semigroup:Ordering = Semigroup: λ where
    LT _ -> LT
    EQ y -> y
    GT _ -> GT

  -- Ordering is a monoid.
  open import Data.Monoid
  Monoid:Ordering : Monoid Ordering
  Monoid:Ordering = Monoid: EQ

-- An instance of type Ord X signifies that X is totally ordered.
open import Data.Bool
open import Data.Eq
record Ord (X : Set) : Set where
  constructor Ord:
  field
    {{instance:Eq}} : Eq X
    _<_ : X -> X -> Bool

  compare : X -> X -> Ordering
  compare x y = 
    if x == y then EQ else
    if x < y then LT else GT
  
  _<=_ : X -> X -> Bool
  x <= y = (x == y) || (x < y)

  _>_ : X -> X -> Bool
  x > y = y < x

  _>=_ : X -> X -> Bool
  x >= y = (x == y) || (x > y)

  min : X -> X -> X 
  min x y = if x < y then x else y

  max : X -> X -> X 
  max x y = if x > y then x else y

open Ord {{...}} public

-- A useful combinator for comparing.
comparing : {X Y : Set} {{_ : Ord Y}}
  -> (X -> Y) -> X -> X -> Ordering
comparing p x y = compare (p x) (p y)
