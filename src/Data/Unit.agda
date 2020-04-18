{-# OPTIONS --type-in-type #-}

module Data.Unit where

open import Data.Eq
open import Data.Monoid
open import Data.Ord
open import Data.Ring
open import Data.Semigroup
open import Data.Semiring
open import Prim

instance
  eqUnit : Eq Unit
  eqUnit ._==_ unit unit = true

  ordUnit : Ord Unit
  ordUnit ._<_ unit unit = false

  semigroupUnit : Semigroup Unit
  semigroupUnit ._<>_ unit unit = unit

  monoidUnit : Monoid Unit
  monoidUnit .mempty = unit
