{-# OPTIONS --type-in-type #-}

module Data.Monoid where

open import Data.Semigroup
open import Prim

private variable A : Set

record Monoid (A : Set) : Set where
  field
    overlap {{super}} : Semigroup A
    mempty : A

  when : Bool -> A -> A
  when true x = x
  when false _ = mempty

  unless : Bool -> A -> A
  unless true _ = mempty
  unless false x = x

open Monoid {{...}} public

instance
  monoidDual : {{_ : Monoid A}} -> Monoid (Dual A)
  monoidDual .mempty = toDual mempty

  monoidFirst : {{_ : Monoid A}} -> Monoid (First A)
  monoidFirst .mempty = toFirst mempty

  monoidLast : {{_ : Monoid A}} -> Monoid (Last A)
  monoidLast .mempty = toLast mempty
