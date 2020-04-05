{-# OPTIONS --type-in-type #-}

module Data.Semiring where

open import Data.Bool using (IsTrue)
open import Data.Eq using (Eq; _/=_)
open import Data.Monoid using (Monoid; mempty)
open import Data.Semigroup using (Semigroup; _<>_)
open import Data.Unit using (Unit; unit)

private variable A B : Set

record Semiring (A : Set) : Set where
  infixr 6 _+_
  infixr 7 _*_
  field
    zero : A
    one : A
    _+_ : A -> A -> A
    _*_ : A -> A -> A

  Nonzero : {{_ : Eq A}} -> A -> Set
  Nonzero a = IsTrue (a /= zero)

open Semiring {{...}} public

record Sum (A : Set) : Set where
  constructor toSum
  field fromSum : A

open Sum public

record Product (A : Set) : Set where
  constructor toProduct
  field fromProduct : A

open Product public

instance
  semiringUnit : Semiring Unit
  semiringUnit .zero = unit
  semiringUnit .one = unit
  semiringUnit ._+_ _ _ = unit
  semiringUnit ._*_ _ _ = unit

  semiringFunction : {{_ : Semiring B}} -> Semiring (A -> B)
  semiringFunction .zero _ = zero
  semiringFunction .one _ = one
  semiringFunction ._+_ f g x = f x + g x
  semiringFunction ._*_ f g x = f x * g x

  semigroupSum : {{_ : Semiring A}} -> Semigroup (Sum A)
  semigroupSum ._<>_ x y = toSum (fromSum x + fromSum y)

  semigroupProduct : {{_ : Semiring A}} -> Semigroup (Product A)
  semigroupProduct ._<>_ x y = toProduct (fromProduct x * fromProduct y)

  monoidSum : {{_ : Semiring A}} -> Monoid (Sum A)
  monoidSum .mempty = toSum zero

  monoidProduct : {{_ : Semiring A}} -> Monoid (Product A)
  monoidProduct .mempty = toProduct one
