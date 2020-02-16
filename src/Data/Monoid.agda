{-# OPTIONS --type-in-type #-}

module Data.Monoid where

-- A semigroup is a monoid when its binary operation has an identity.

open import Data.Semigroup public

record Monoid (X : Set) : Set where
  constructor Monoid:
  field
    overlap {{Semigroup:Monoid}} : Semigroup X
    mempty : X

open Monoid {{...}} public

-- Every monoid instance has an opposite version.

open import Notation.Dual public

instance
  Dual:Monoid : forall {X} -> Dual (Monoid X)
  Dual:Monoid .Op monoid = let instance inst = monoid in \ where
    .Semigroup:Monoid -> Op (Semigroup:Monoid {{inst}})
    .mempty -> mempty
