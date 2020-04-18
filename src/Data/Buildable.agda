{-# OPTIONS --type-in-type #-}

module Data.Buildable where

open import Data.Monoid
open import Data.Semigroup

record IsBuildable (S A : Set) : Set where
  infixr 5 _++_
  field
    {{monoid}} : Monoid S
    singleton : A -> S

  nil : S
  nil = mempty

  _++_ : S -> S -> S
  _++_ = _<>_

open IsBuildable {{...}} public

Buildable : (Set -> Set) -> Set
Buildable F = forall {A} -> IsBuildable (F A) A
