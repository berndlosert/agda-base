{-# OPTIONS --type-in-type #-}

module Data.Int where

open import Data.Bool
open import Data.Ord
open import Data.Nat
open import Data.Num
open import Data.Unit
open import Data.Void

private variable A : Set

open import Agda.Builtin.Int public
  using (Int; pos; negsuc)

foldZ : (Nat -> A) -> (Nat -> A) -> Int -> A
foldZ f g (pos n) = f n
foldZ f g (negsuc n) = g n

private
  subNat : Nat -> Nat -> Int
  subNat m 0 = pos m
  subNat 0 (suc n) = negsuc n
  subNat (suc m) (suc n) = subNat m n

  negNat : Nat -> Int
  negNat n = subNat 0 n

  neg : Int -> Int
  neg (pos 0) = pos 0
  neg (pos (suc n)) = negsuc n
  neg (negsuc n) = pos (suc n)

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
    (negsuc m) (pos n) -> subNat n (suc m)
    (pos m) (negsuc n) -> subNat m (suc n)
    (pos m) (pos n) -> pos (m + n)
  semiringInt ._*_ = \ where
    (pos n) (pos m) -> pos (n * m)
    (negsuc n) (negsuc m) -> pos (suc n * suc m)
    (pos n) (negsuc m) -> negNat (n * suc m)
    (negsuc n) (pos m) -> negNat (suc n * m)

  ringInt : Ring Int
  ringInt ._-_ n m = n + (neg m)

  numInt : Num Int
  numInt .Nonzero (pos 0) = Void
  numInt .Nonzero _ = Unit
  numInt ._/_ = \ where
    (pos n) (pos m@(suc m-1)) -> pos (n / m)
    (negsuc n) (negsuc m) -> pos (suc n / suc m)
    (pos n) (negsuc m) -> negNat (n / suc m)
    (negsuc n) (pos m@(suc m-1)) -> negNat (suc n / m)
  numInt ._%_ = \ where
    (pos n) (pos m@(suc m-1)) -> pos (n % m)
    (negsuc n) (negsuc m) -> pos (suc n % suc m)
    (pos n) (negsuc m) -> negNat (n % suc m)
    (negsuc n) (pos m@(suc m-1)) -> negNat (suc n % m)
