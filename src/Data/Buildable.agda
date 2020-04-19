{-# OPTIONS --type-in-type #-}

module Data.Buildable where

open import Data.Monoid
open import Data.Semigroup

record IsBuildable (S A : Set) : Set where
  field
    {{monoid}} : Monoid S
    singleton : A -> S

  infixr 5 _++_
  _++_ : S -> S -> S
  _++_ = _<>_

  nil : S
  nil = mempty

  cons : A -> S -> S
  cons a s = singleton a ++ s

  snoc : S -> A -> S
  snoc s a = s ++ singleton a

open IsBuildable {{...}} public

Buildable : (Set -> Set) -> Set
Buildable F = forall {A} -> IsBuildable (F A) A
