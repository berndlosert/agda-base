{-# OPTIONS --type-in-type #-}

module Data.Semiring where

open import Data.Monoid
open import Data.Semigroup
open import Data.Type.Equality
open import Prim

private variable A B : Set

record Semiring (A : Set) : Set where
  infixr 6 _+_
  infixr 7 _*_
  field
    zero : A
    one : A
    _+_ : A -> A -> A
    _*_ : A -> A -> A
    Nonzero : A -> Set

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
  semigroupSum : {{_ : Semiring A}} -> Semigroup (Sum A)
  semigroupSum ._<>_ x y = toSum (fromSum x + fromSum y)

  semigroupProduct : {{_ : Semiring A}} -> Semigroup (Product A)
  semigroupProduct ._<>_ x y = toProduct (fromProduct x * fromProduct y)

  monoidSum : {{_ : Semiring A}} -> Monoid (Sum A)
  monoidSum .mempty = toSum zero

  monoidProduct : {{_ : Semiring A}} -> Monoid (Product A)
  monoidProduct .mempty = toProduct one
