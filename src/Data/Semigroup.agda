{-# OPTIONS --type-in-type #-}

module Data.Semigroup where

open import Data.Bool using (Bool; true; false; _&&_; _||_)
open import Data.Function using (_<<<_)
open import Data.Unit using (Unit; unit)
open import Data.Void using (Void)

private variable A B : Set

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

record Endo A : Set where
  constructor toEndo
  field fromEndo : A -> A

open Endo public

instance
  semigroupDual : {{_ : Semigroup A}} -> Semigroup (Dual A)
  semigroupDual ._<>_ (toDual x) (toDual y) = toDual (y <> x)

  semigroupFirst : Semigroup (First A)
  semigroupFirst ._<>_ x y = x

  semigroupLast : Semigroup (Last A)
  semigroupLast ._<>_ x y = y

  semigroupVoid : Semigroup Void
  semigroupVoid ._<>_ = \ ()

  semigroupUnit : Semigroup Unit
  semigroupUnit ._<>_ unit unit = unit

  semigroupAll : Semigroup All
  semigroupAll ._<>_ x y = toAll (fromAll x && fromAll y)

  semigroupAny : Semigroup Any
  semigroupAny ._<>_ x y = toAny (fromAny x || fromAny y)

  semigroupFunction : {{_ : Semigroup B}} -> Semigroup (A -> B)
  semigroupFunction ._<>_ f g = \ a -> f a <> g a

  semigroupEndo : Semigroup (Endo A)
  semigroupEndo ._<>_ g f = toEndo (fromEndo g <<< fromEndo f)
