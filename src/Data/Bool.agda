{-# OPTIONS --type-in-type #-}

module Data.Bool where

open import Data.Eq
open import Data.Monoid
open import Data.Semigroup
open import Prim

-- Bool semigroup where x <> y = x && y.
record All : Set where
  constructor toAll
  field fromAll : Bool

open All public

-- Bool semigroup where x <> y = x || y.
record Any : Set where
  constructor toAny
  field fromAny : Bool

open Any public

instance
  eqBool : Eq Bool
  eqBool ._==_ = \ where
    true true -> true
    false false -> false
    _ _ -> false

  semigroupAll : Semigroup All
  semigroupAll ._<>_ x y = toAll (fromAll x && fromAll y)

  semigroupAny : Semigroup Any
  semigroupAny ._<>_ x y = toAny (fromAny x || fromAny y)

  monoidAll : Monoid All
  monoidAll .mempty = toAll true

  monoidAny : Monoid Any
  monoidAny .mempty = toAny false
