{-# OPTIONS --type-in-type #-}

module Data.Semigroup where

open import Control.Applicative
open import Control.Monad
open import Data.Functor
open import Data.Ord
open import Prim

private variable A : Set

--------------------------------------------------------------------------------
-- Semigroup
--------------------------------------------------------------------------------

record Semigroup (A : Set) : Set where
  infixr 5 _<>_
  field _<>_ : A -> A -> A

open Semigroup {{...}} public

--------------------------------------------------------------------------------
-- Sum
--------------------------------------------------------------------------------

-- Additive semigroups
record Sum (A : Set) : Set where
  constructor toSum
  field fromSum : A

open Sum public

infixr 6 _+_
_+_ : {{_ : Semigroup (Sum A)}} -> A -> A -> A
x + y = fromSum (toSum x <> toSum y)

instance
  functorSum : Functor Sum
  functorSum .map f = toSum <<< f <<< fromSum

  applicativeSum : Applicative Sum
  applicativeSum .pure = toSum
  applicativeSum ._<*>_ f x = toSum $ fromSum f (fromSum x)

  monadSum : Monad Sum
  monadSum ._>>=_ m k = k (fromSum m)

--------------------------------------------------------------------------------
-- Product
--------------------------------------------------------------------------------

-- Multiplicative semigroups
record Product (A : Set) : Set where
  constructor toProduct
  field fromProduct : A

open Product public

infixr 7 _*_
_*_ : {{_ : Semigroup (Product A)}} -> A -> A -> A
x * y = fromProduct (toProduct x <> toProduct y)

instance
  functorProduct : Functor Product
  functorProduct .map f = toProduct <<< f <<< fromProduct

  applicativeProduct : Applicative Product
  applicativeProduct .pure = toProduct
  applicativeProduct ._<*>_ f x = toProduct $ fromProduct f (fromProduct x)

  monadProduct : Monad Product
  monadProduct ._>>=_ m k = k (fromProduct m)

--------------------------------------------------------------------------------
-- Dual
--------------------------------------------------------------------------------

-- Dual semigroups
record Dual (A : Set) : Set where
  constructor toDual
  field fromDual : A

open Dual public

instance
  semigroupDual : {{_ : Semigroup A}} -> Semigroup (Dual A)
  semigroupDual ._<>_ x y = toDual $ fromDual y <> fromDual x

  functorDual : Functor Dual
  functorDual .map f = toDual <<< f <<< fromDual

  applicativeDual : Applicative Dual
  applicativeDual .pure = toDual
  applicativeDual ._<*>_ f x = toDual $ fromDual f (fromDual x)

  monadDual : Monad Dual
  monadDual ._>>=_ m k = k (fromDual m)

--------------------------------------------------------------------------------
-- First
--------------------------------------------------------------------------------

-- Semigroup where x <> y = x
record First (A : Set) : Set where
  constructor toFirst
  field fromFirst : A

open First public

instance
  semigroupFirst : Semigroup (First A)
  semigroupFirst ._<>_ x y = x

  functorFirst : Functor First
  functorFirst .map f = toFirst <<< f <<< fromFirst

  applicativeFirst : Applicative First
  applicativeFirst .pure = toFirst
  applicativeFirst ._<*>_ f x = toFirst $ fromFirst f (fromFirst x)

  monadFirst : Monad First
  monadFirst ._>>=_ m k = k (fromFirst m)

--------------------------------------------------------------------------------
-- Last
--------------------------------------------------------------------------------

-- Semigroup where x <> y = y
record Last (A : Set) : Set where
  constructor toLast
  field fromLast : A

open Last public

instance
  semigroupLast : Semigroup (Last A)
  semigroupLast ._<>_ x y = y

  functorLast : Functor Last
  functorLast .map f = toLast <<< f <<< fromLast

  applicativeLast : Applicative Last
  applicativeLast .pure = toLast
  applicativeLast ._<*>_ f x = toLast $ fromLast f (fromLast x)

  monadLast : Monad Last
  monadLast ._>>=_ m k = k (fromLast m)

--------------------------------------------------------------------------------
-- Min
--------------------------------------------------------------------------------

-- Semigroup where x <> y = min x y
record Min (A : Set) : Set where
  constructor toMin
  field fromMin : A

open Min public

instance
  semigroupMin : {{_ : Ord A}} -> Semigroup (Min A)
  semigroupMin ._<>_ x y = toMin $ min (fromMin x) (fromMin y)

  functorMin : Functor Min
  functorMin .map f = toMin <<< f <<< fromMin

  applicativeMin : Applicative Min
  applicativeMin .pure = toMin
  applicativeMin ._<*>_ f x = toMin $ fromMin f (fromMin x)

  monadMin : Monad Min
  monadMin ._>>=_ m k = k (fromMin m)

--------------------------------------------------------------------------------
-- Max
--------------------------------------------------------------------------------

-- Semigroup where x <> y = max x y
record Max (A : Set) : Set where
  constructor toMax
  field fromMax : A

open Max public

instance
  semigroupMax : {{_ : Ord A}} -> Semigroup (Max A)
  semigroupMax ._<>_ x y = toMax $ max (fromMax x) (fromMax y)

  functorMax : Functor Max
  functorMax .map f = toMax <<< f <<< fromMax

  applicativeMax : Applicative Max
  applicativeMax .pure = toMax
  applicativeMax ._<*>_ f x = toMax $ fromMax f (fromMax x)

  monadMax : Monad Max
  monadMax ._>>=_ m k = k (fromMax m)
