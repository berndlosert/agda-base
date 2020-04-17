{-# OPTIONS --type-in-type #-}

module Data.Ord where

open import Data.Eq
open import Prim

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
  x <= y = if x < y then true else if x == y then true else false

  infixl 4 _>_
  _>_ : A -> A -> Bool
  _>_ = flip _<_

  infixl 4 _>=_
  _>=_ : A -> A -> Bool
  _>=_ = flip _<=_

  min : A -> A -> A
  min x y = if x < y then x else y

  max : A -> A -> A
  max x y = if x < y then y else x

  comparing : (B -> A) -> B -> B -> Ordering
  comparing p x y = compare (p x) (p y)

open Ord {{...}} public
