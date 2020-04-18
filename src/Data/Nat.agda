{-# OPTIONS --type-in-type #-}

module Data.Nat where

import Agda.Builtin.Nat
open import Data.Eq
open import Data.Euclidean
open import Data.Monoid
open import Data.Ord
open import Data.Semigroup
open import Data.Semiring
open import Prim

private variable A : Set

natrec : A -> (Nat -> A -> A) -> Nat -> A
natrec a _ 0 = a
natrec a h n@(suc n-1) = h n-1 (natrec a h n-1)

applyN : (A -> A) -> Nat -> A -> A
applyN f n a = natrec a (const f) n

monus : Nat -> Nat -> Nat
monus = Agda.Builtin.Nat._-_

instance
  eqNat : Eq Nat
  eqNat ._==_ = Agda.Builtin.Nat._==_

  ordNat : Ord Nat
  ordNat ._<_ = Agda.Builtin.Nat._<_

  semigroupSumNat : Semigroup (Sum Nat)
  semigroupSumNat ._<>_ m n =
    toSum $ Agda.Builtin.Nat._+_ (fromSum m) (fromSum n)

  semigroupProductNat : Semigroup (Product Nat)
  semigroupProductNat ._<>_ m n =
    toProduct $ Agda.Builtin.Nat._*_ (fromProduct m) (fromProduct n)

  monoidSumNat : Monoid (Sum Nat)
  monoidSumNat .mempty = toSum 0

  monoidProductNat : Monoid (Product Nat)
  monoidProductNat .mempty = toProduct 1

  semiringNat : Semiring Nat
  semiringNat .Nonzero 0 = Void
  semiringNat .Nonzero (suc _) = Unit

  euclideanNat : Euclidean Nat
  euclideanNat .degree n = n
  euclideanNat .quot m 0 = 0 -- unreachable
  euclideanNat .quot m (suc n) = Agda.Builtin.Nat.div-helper 0 n m n
  euclideanNat .mod m 0 = 0 -- unreachable
  euclideanNat .mod m (suc n) = Agda.Builtin.Nat.mod-helper 0 n m n
