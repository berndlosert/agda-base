{-# OPTIONS --type-in-type #-}

module Data.Fin where

open import Data.Bool
open import Data.Cast
open import Data.Nat
open import Data.Void

-- The type Fin n is a type with n elements.
data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc : {n : Nat} -> Fin n -> Fin (suc n)

instance
  FinToNat : {n : Nat} -> Cast (Fin n) Nat
  FinToNat .cast zero = zero
  FinToNat .cast (suc n) = suc (cast n)

-- Unfortunately, we cannot use this to define a Cast Nat (Fin (suc n))
-- instance because cast is nondependent.
fin : (n : Nat) -> Fin (suc n)
fin zero  = zero
fin (suc n) = suc (fin n)

private
  fromN : ∀ m n -> cast (m <= n) -> Fin (suc n)
  fromN zero _ _ = zero
  fromN (suc _) zero ()
  fromN (suc m) (suc n) p = suc (fromN m n p)

instance
  Number:Fin : ∀ {n} -> Number (Fin (suc n))
  Number:Fin {n} = record {
      Constraint = \ m -> cast (m <= n);
      fromNat = \ m {{p}} -> fromN m n p 
    }
