{-# OPTIONS --type-in-type #-}

module Data.Monoid where

-- A semigroup is a monoid when its binary operation has an identity.

open import Data.Semigroup public

record Monoid (X : Set) : Set where
  constructor monoid
  field
    overlap {{semigroupMonoid}} : Semigroup X
    empty : X

open Monoid {{...}} public

-- Every monoid instance has an opposite version.

open import Notation.Dual public

instance
  Dual:Monoid : forall {X} -> Dual (Monoid X)
  Dual:Monoid .Op monoid = let instance inst = monoid in \ where
    .semigroupMonoid -> Op (semigroupMonoid {{inst}})
    .empty -> empty
