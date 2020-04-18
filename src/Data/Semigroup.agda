{-# OPTIONS --type-in-type #-}

module Data.Semigroup where

open import Data.Ord
open import Prim

private variable A : Set

record Semigroup (A : Set) : Set where
  infixr 5 _<>_
  field _<>_ : A -> A -> A

open Semigroup {{...}} public

-- Additive semigroups
record Sum (A : Set) : Set where
  constructor toSum
  field fromSum : A

open Sum public

infixr 6 _+_
_+_ : {{_ : Semigroup (Sum A)}} -> A -> A -> A
x + y = fromSum (toSum x <> toSum y)

-- Multiplicative semigroups
record Product (A : Set) : Set where
  constructor toProduct
  field fromProduct : A

open Product public

infixr 7 _*_
_*_ : {{_ : Semigroup (Product A)}} -> A -> A -> A
x * y = fromProduct (toProduct x <> toProduct y)

-- Dual semigroups
record Dual (A : Set) : Set where
  constructor toDual
  field fromDual : A

open Dual public

-- Semigroup where x <> y = x
record First (A : Set) : Set where
  constructor toFirst
  field fromFirst : A

open First public

-- Semigroup where x <> y = y
record Last (A : Set) : Set where
  constructor toLast
  field fromLast : A

open Last public

-- Semigroup where x <> y = min x y
record Min (A : Set) : Set where
  constructor toMin
  field fromMin : A

open Min public

-- Semigroup where x <> y = max x y
record Max (A : Set) : Set where
  constructor toMax
  field fromMax : A

open Max public

instance
  semigroupDual : {{_ : Semigroup A}} -> Semigroup (Dual A)
  semigroupDual ._<>_ x y = toDual $ fromDual y <> fromDual x

  semigroupFirst : Semigroup (First A)
  semigroupFirst ._<>_ x y = x

  semigroupLast : Semigroup (Last A)
  semigroupLast ._<>_ x y = y

  semigroupMin : {{_ : Ord A}} -> Semigroup (Min A)
  semigroupMin ._<>_ x y = toMin $ min (fromMin x) (fromMin y)

  semigroupMax : {{_ : Ord A}} -> Semigroup (Max A)
  semigroupMax ._<>_ x y = toMax $ max (fromMax x) (fromMax y)
