{-# OPTIONS --type-in-type #-}

module Data.Monoid where

open import Data.Bool
open import Data.Function
open import Data.Semigroup public
open import Data.Unit

private variable A B : Set

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

  monoidFunction : {{_ : Monoid B}} -> Monoid (A -> B)
  monoidFunction .mempty = const mempty

  monoidEndo : Monoid (Endo A)
  monoidEndo .mempty = toEndo id
