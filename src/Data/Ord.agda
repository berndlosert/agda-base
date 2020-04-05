{-# OPTIONS --type-in-type #-}

module Data.Ord where

open import Data.Bool using (Bool; false; if_then_else_; _||_)
open import Data.Eq using (Eq; _==_; _/=_)
open import Data.Unit using (Unit; unit)
open import Data.Void using (Void)

private variable B : Set

data Ordering : Set where
  LT EQ GT : Ordering

record Ord (A : Set) : Set where
  infixl 4 _<_
  field
    overlap {{eq}} : Eq A
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
