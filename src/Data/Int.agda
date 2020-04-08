{-# OPTIONS --type-in-type #-}

module Data.Int where

private variable A : Set

module Int where
  open import Agda.Builtin.Int public
    using (Int; pos; negsuc)
    renaming (primShowInteger to show)

  open import Data.Nat

  open import Prelude
    hiding (Nonzero)

  foldZ : (Nat -> A) -> (Nat -> A) -> Int -> A
  foldZ f g (pos n) = f n
  foldZ f g (negsuc n) = g n

  eq : Int -> Int -> Bool
  eq (pos m) (pos n) = m == n
  eq (negsuc m) (negsuc n) = m == n
  eq _ _ = false

  lt : Int -> Int -> Bool
  lt (pos m) (pos n) = m < n
  lt (negsuc m) (negsuc n) = m > n
  lt (negsuc _) (pos _) = true
  lt (pos _) (negsuc _) = false

  subNat : Nat -> Nat -> Int
  subNat m 0 = pos m
  subNat 0 (suc n) = negsuc n
  subNat (suc m) (suc n) = subNat m n

  negNat : Nat -> Int
  negNat n = subNat 0 n

  add : Int -> Int -> Int
  add (negsuc m) (negsuc n) = negsuc (suc (m + n))
  add (negsuc m) (pos n) = subNat n (suc m)
  add (pos m) (negsuc n) = subNat m (suc n)
  add (pos m) (pos n) = pos (m + n)

  mul : Int -> Int -> Int
  mul (pos n) (pos m) = pos (n * m)
  mul (negsuc n) (negsuc m) = pos (suc n * suc m)
  mul (pos n) (negsuc m) = negNat (n * suc m)
  mul (negsuc n) (pos m) = negNat (suc n * m)

  neg : Int -> Int
  neg (pos 0) = pos zero
  neg (pos (suc n)) = negsuc n
  neg (negsuc n) = pos (suc n)

  sub : Int -> Int -> Int
  sub n m = add n (neg m)

  Nonzero : Int -> Set
  Nonzero (pos 0) = Void
  Nonzero _ = Unit

  div : (n m : Int) {_ : Nonzero m} -> Int
  div (pos n) (pos m@(suc m-1)) = pos (n / m)
  div (negsuc n) (negsuc m) = pos (suc n / suc m)
  div (pos n) (negsuc m) = negNat (n / suc m)
  div (negsuc n) (pos m@(suc m-1)) = negNat (suc n / m)

  mod : (n m : Int) {_ : Nonzero m} -> Int
  mod (pos n) (pos m@(suc m-1)) = pos (n % m)
  mod (negsuc n) (negsuc m) = pos (suc n % suc m)
  mod (pos n) (negsuc m) = negNat (n % suc m)
  mod (negsuc n) (pos m@(suc m-1)) = negNat (suc n % m)

open Int public
  using (Int; pos; negsuc)
  hiding (module Int)

open import Prelude

instance
  eqInt : Eq Int
  eqInt ._==_ = Int.eq

  ordInt : Ord Int
  ordInt ._<_ = Int.lt

  semiringInt : Semiring Int
  semiringInt .zero = pos 0
  semiringInt .one = pos 1
  semiringInt ._+_ = Int.add
  semiringInt ._*_ = Int.mul

  ringInt : Ring Int
  ringInt ._-_ = Int.sub

  numInt : Num Int
  numInt .Nonzero = Int.Nonzero
  numInt ._/_ = Int.div
  numInt ._%_ = Int.mod
