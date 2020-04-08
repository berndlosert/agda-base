{-# OPTIONS --type-in-type #-}

module Data.Ord where

open import Data.Bool
open import Data.Eq public
open import Data.Unit
open import Data.Void

private variable B : Set

data Ordering : Set where
  LT EQ GT : Ordering

record Ord (A : Set) : Set where
  infixl 4 _<_
  field
    overlap {{super}} : Eq A
    _<_ : A -> A -> Bool

  compare : A -> A -> Ordering
  compare x y = if x < y then LT else if x == y then EQ else GT

  infixl 4 _<=_
  _<=_ : A -> A -> Bool
  x <= y = (x < y) || (x == y)

  infixl 4 _>_
  _>_ : A -> A -> Bool
  x > y = y < x

  infixl 4 _>=_
  _>=_ : A -> A -> Bool
  x >= y = y <= x

  min : A -> A -> A
  min x y = if x < y then x else y

  max : A -> A -> A
  max x y = if x < y then y else x

  comparing : (B -> A) -> B -> B -> Ordering
  comparing p x y = compare (p x) (p y)

open Ord {{...}} public

instance
  ordVoid : Ord Void
  ordVoid ._<_ = \ ()

  ordUnit : Ord Unit
  ordUnit ._<_ unit unit = false
