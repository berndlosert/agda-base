{-# OPTIONS --type-in-type #-}

module Data.Int where

open import Data.Eq
open import Data.Nat
open import Data.Ord
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

  semiringInt : Semiring Int
  semiringInt .zero = pos 0
  semiringInt .one = pos 1
  semiringInt ._+_ = \ where
    (negsuc m) (negsuc n) -> negsuc (suc (m + n))
    (negsuc m) (pos n) -> sub n (suc m)
    (pos m) (negsuc n) -> sub m (suc n)
    (pos m) (pos n) -> pos (m + n)
  semiringInt ._*_ = \ where
    (pos n) (pos m) -> pos (n * m)
    (negsuc n) (negsuc m) -> pos (suc n * suc m)
    (pos n) (negsuc m) -> neg (n * suc m)
    (negsuc n) (pos m) -> neg (suc n * m)
  semiringInt .Nonzero (pos 0) = Void
  semiringInt .Nonzero _ = Unit

  ringInt : Ring Int
  ringInt .-_ = \ where
    (pos 0) -> pos 0
    (pos (suc n)) -> negsuc n
    (negsuc n) -> pos (suc n)
  ringInt ._-_ n m = n + (- m)
