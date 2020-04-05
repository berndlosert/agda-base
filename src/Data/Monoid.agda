{-# OPTIONS --type-in-type #-}

module Data.Monoid where

open import Data.Bool using (Bool; true; false; not)
open import Data.Semigroup using (Semigroup; Dual; toDual)
open import Data.Semigroup using (First; toFirst)
open import Data.Semigroup using (All; toAll; Any; toAny)
open import Data.Unit using (Unit; unit)

private variable A : Set

record Monoid (A : Set) : Set where
  field
    overlap {{super}} : Semigroup A
    mempty : A

  when : Bool -> A -> A
  when true x = x
  when false _ = mempty

  unless : Bool -> A -> A
  unless b = when (not b)

open Monoid {{...}} public

instance
  monoidDual : {{_ : Monoid A}} -> Monoid (Dual A)
  monoidDual .mempty = toDual mempty

  monoidFirst : {{_ : Monoid A}} -> Monoid (First A)
  monoidFirst .mempty = toFirst mempty

  monoidUnit : Monoid Unit
  monoidUnit .mempty = unit

  monoidAll : Monoid All
  monoidAll .mempty = toAll true

  monoidAny : Monoid Any
  monoidAny .mempty = toAny false
