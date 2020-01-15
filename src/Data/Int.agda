{-# OPTIONS --type-in-type #-}

module Data.Int where

-- The type Int of integers has two constructors: nonneg : Nat -> Int and
-- negsuc : Nat -> Int. The value nonneg n represents the nonnegitive integer n.
-- The value negsuc n represents the negative integer -n - 1.

open import Agda.Builtin.Int public
  using (Int; negsuc)
  renaming (pos to nonneg)
  hiding (module Int)

-- Negation of integers.

open import Data.Nat public
open import Notation.Negation public

instance
  Negation:Int : Negation Int
  Negation:Int = Negation: \ where
    (nonneg zero) -> nonneg zero
    (nonneg (suc n)) -> negsuc n
    (negsuc n) -> nonneg (suc n)

-- Int equality.

open import Data.Eq public

instance
  Eq:Int : Eq Int
  Eq:Int = Eq: \ where
    (nonneg n) (nonneg m) -> n == m
    (negsuc n) (negsuc m) -> n == m
    _ _ -> false

-- Comparing Int values.

open import Data.Ord public

instance
  Ord:Int : Ord Int
  Ord:Int = Ord: \ where
    (nonneg n) (nonneg m) -> n < m
    (nonneg n) (negsuc m) -> false
    (negsuc n) (nonneg m) -> true
    (negsuc n) (negsuc m) -> n < m

-- Int addition.

open import Data.Function
open import Notation.Add public

instance
  Add:Int : Add Int
  Add:Int = Add: add
    where
      -- Subtracting two naturals to an integer result.
      sub : Nat -> Nat -> Int
      sub m 0 = nonneg m
      sub 0 (suc n) = negsuc n
      sub (suc m) (suc n) = sub m n

      add : Int -> Int -> Int
      add (negsuc m) (negsuc n) = negsuc (suc (m + n))
      add (negsuc m) (nonneg n) = sub n (suc m)
      add (nonneg m) (negsuc n) = sub m (suc n)
      add (nonneg m) (nonneg n) = nonneg (m + n)

-- Int multiplication.

open import Notation.Mul public

instance
  Mul:Int : Mul Int
  Mul:Int = Mul: \ where
    (nonneg n) (nonneg m) -> nonneg (n * m)
    (negsuc n) (negsuc m) -> nonneg (suc n * suc m)
    (nonneg n) (negsuc m) -> - (nonneg (n * suc m))
    (negsuc n) (nonneg m) -> - (nonneg (suc n * m))

-- Int subtraction.

open import Notation.Sub public

instance
  Sub:Int : Sub Int
  Sub:Int = Sub: \ n m -> n + (- m)

module Int where

  -- Convert an Int to a Nat (basically the absolute value).

  toNat : Int -> Nat
  toNat (nonneg n) = n
  toNat (negsuc n) = suc n

  -- The absolute value of an Int.

  abs : Int -> Int
  abs n = nonneg (toNat n)

  -- Determine if a integer is even or odd.

  even : Int -> Bool
  even (nonneg n) = Nat.even n
  even (negsuc n) = Nat.odd n

  odd : Int -> Bool
  odd n = not (even n)
