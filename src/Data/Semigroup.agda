{-# OPTIONS --type-in-type #-}

module Data.Semigroup where

open import Prim

private variable A : Set

record Semigroup (A : Set) : Set where
  infixr 5 _<>_
  field _<>_ : A -> A -> A

open Semigroup {{...}} public

-- Dual semigroups.
record Dual (A : Set) : Set where
  constructor toDual
  field fromDual : A

open Dual public

-- Semigroup were x <> y = x.
record First (A : Set) : Set where
  constructor toFirst
  field fromFirst : A

open First public

-- Semigroup were x <> y = y.
record Last (A : Set) : Set where
  constructor toLast
  field fromLast : A

open Last public

instance
  semigroupDual : {{_ : Semigroup A}} -> Semigroup (Dual A)
  semigroupDual ._<>_ x y = toDual (fromDual y <> fromDual x)

  semigroupFirst : Semigroup (First A)
  semigroupFirst ._<>_ x y = x

  semigroupLast : Semigroup (Last A)
  semigroupLast ._<>_ x y = y
