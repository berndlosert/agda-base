{-# OPTIONS --type-in-type #-}

module Data.Int where

-- The type Int of integers has two constructors: pos : Nat -> Int and
-- negsuc : Nat -> Int. The value pos n represents the positive integer n.
-- The value negsuc n represents the negative integer -n - 1.

open import Agda.Builtin.Int public
  using (Int; pos; negsuc)
  hiding (module Int)

module Int where

  -- Allows us to write -n for negative integers.

  open import Data.Nat
  open import Data.Unit
  open import Notation.Negative
  
  instance
    Negative:Int : Negative Int
    Negative:Int = record {
        Constraint = \ _ -> Unit;
        fromNeg = \ where
          0 -> pos zero
          (suc n) -> negsuc n
      }

  -- Convert an Int to a Nat (basically the absolute value).

  toNat : Int -> Nat 
  toNat (pos n) = n
  toNat (negsuc n) = suc n
  
  -- The absolute value of an Int.

  abs : Int -> Int
  abs n = pos (toNat n)

  -- Negate a Nat to an Int.

  neg : Nat -> Int
  neg zero = pos (zero)
  neg (suc n) = negsuc n
 
  -- Negation of integers.

  instance
    Negation:Int : Negation Int
    Negation:Int = Negation: \ where
      (pos zero) -> pos zero
      (pos (suc n)) -> negsuc n
      (negsuc n) -> pos (suc n)
  
  -- Int equality.

  open import Data.Bool
  open import Data.Eq

  instance
    Eq:Int : Eq Int
    Eq:Int = Eq: \ where
      (pos n) (pos m) -> n == m
      (negsuc n) (negsuc m) -> n == m
      _ _ -> false
  
  -- Comparing Int values.

  open import Data.Ord

  instance
    Ord:Int : Ord Int
    Ord:Int = Ord: \ where
      (pos n) (pos m) -> n < m
      (pos n) (negsuc m) -> false
      (negsuc n) (pos m) -> true
      (negsuc n) (negsuc m) -> n < m
  
  -- Int addition.

  open import Notation.Add
  open import Data.Function

  instance
    Add:Int : Add Int
    Add:Int = Add: add
      where
        -- Subtracting two naturals to an integer result.
        sub : Nat -> Nat -> Int
        sub m 0 = pos m
        sub 0 (suc n) = negsuc n
        sub (suc m) (suc n) = sub m n
    
        add : Int -> Int -> Int
        add (negsuc m) (negsuc n) = negsuc (suc (m + n))
        add (negsuc m) (pos n) = sub n (suc m)
        add (pos m) (negsuc n) = sub m (suc n)
        add (pos m) (pos n) = pos (m + n)
  
  -- Int multiplication.

  open import Notation.Mul

  instance
    Mul:Int : Mul Int
    Mul:Int = Mul: \ where
      (pos n) (pos m) -> pos (n * m)
      (negsuc n) (negsuc m) -> pos (suc n * suc m)
      (pos n) (negsuc m) -> - (pos (n * suc m))
      (negsuc n) (pos m) -> - (pos (suc n * m))
  
  -- Int subtraction.

  open import Notation.Sub

  instance
    Sub:Int : Sub Int
    Sub:Int = Sub: \ n m -> n + (- m)
  
  -- Determine if a integer is even or odd.

  even : Int -> Bool
  even (pos n) = Nat.even n
  even (negsuc n) = Nat.odd n

  odd : Int -> Bool
  odd n = not (even n)

open Int public
  using (
    Negative:Int;
    Negation:Int;
    Eq:Int;
    Ord:Int;
    Add:Int;
    Mul:Int;
    Sub:Int 
  )
