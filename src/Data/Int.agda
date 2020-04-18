{-# OPTIONS --type-in-type #-}

module Data.Int where

open import Data.Eq
open import Data.Monoid
open import Data.Nat
open import Data.Ord
open import Data.Semigroup
open import Data.Semiring
open import Data.Ring
open import Prim

private variable A : Set

foldZ : (Nat -> A) -> (Nat -> A) -> Int -> A
foldZ f g (pos n) = f n
foldZ f g (negsuc n) = g n

neg : Nat -> Int
neg 0 = pos 0
neg (suc n) = negsuc n

Nonneg : Int -> Set
Nonneg (pos _) = Unit
Nonneg _ = Void

nonneg : (n : Int) {_ : Nonneg n} -> Nat
nonneg (pos n) = n

private
  sub : Nat -> Nat -> Int
  sub m 0 = pos m
  sub 0 (suc n) = negsuc n
  sub (suc m) (suc n) = sub m n

instance
  eqInt : Eq Int
  eqInt ._==_ = \ where
    (pos m) (pos n) -> m == n
    (negsuc m) (negsuc n) -> m == n
    _ _ -> false

  ordInt : Ord Int
  ordInt ._<_ = \ where
    (pos m) (pos n) -> m < n
    (negsuc m) (negsuc n) -> m > n
    (negsuc _) (pos _) -> true
    (pos _) (negsuc _) -> false

  semigroupSumInt : Semigroup (Sum Int)
  semigroupSumInt ._<>_ x y with fromSum x | fromSum y
  ... | (negsuc m) | (negsuc n) = toSum $ negsuc (suc (m + n))
  ... | (negsuc m) | (pos n) = toSum $ sub n (suc m)
  ... | (pos m) | (negsuc n) = toSum $ sub m (suc n)
  ... | (pos m) | (pos n) = toSum $ pos (m + n)

  semigroupProductInt : Semigroup (Product Int)
  semigroupProductInt ._<>_ x y with fromProduct x | fromProduct y
  ... | (pos n) | (pos m) = toProduct $ pos (n * m)
  ... | (negsuc n) | (negsuc m) = toProduct $ pos (suc n * suc m)
  ... | (pos n) | (negsuc m) = toProduct $ neg (n * suc m)
  ... | (negsuc n) | (pos m) = toProduct $ neg (suc n * m)

  monoidSumInt : Monoid (Sum Int)
  monoidSumInt .mempty = toSum (pos 0)

  monoidProductInt : Monoid (Product Int)
  monoidProductInt .mempty = toProduct (pos 1)

  semiringInt : Semiring Int
  semiringInt .Nonzero (pos 0) = Void
  semiringInt .Nonzero _ = Unit

  ringInt : Ring Int
  ringInt .-_ = \ where
    (pos 0) -> pos 0
    (pos (suc n)) -> negsuc n
    (negsuc n) -> pos (suc n)
  ringInt ._-_ n m = n + (- m)
