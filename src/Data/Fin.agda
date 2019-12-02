{-# OPTIONS --type-in-type #-}

module Data.Fin where

-- The type Fin (suc n) has n + 1 inhabitants, namely 0, 1, ..., n. Note that
-- Fin 0 is effectively the same as Void.

open import Data.Nat

data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc : {n : Nat} -> Fin n -> Fin (suc n)

-- Cast a Fin n into a Nat.

open import Data.Cast

instance
  FinToNat : {n : Nat} -> Cast (Fin n) Nat
  FinToNat .cast zero = zero
  FinToNat .cast (suc n) = suc (cast n)

-- Unfortunately, we cannot use this to define a Cast Nat (Fin (suc n))
-- instance because cast is nondependent.

fin : (n : Nat) -> Fin (suc n)
fin zero  = zero
fin (suc n) = suc (fin n)

-- The Number:Fin instance allows us to write Fin n values using natural
-- number literals.

open import Data.Bool

private
  fromN : forall m n -> cast (m <= n) -> Fin (suc n)
  fromN zero _ _ = zero
  fromN (suc _) zero ()
  fromN (suc m) (suc n) p = suc (fromN m n p)

instance
  Number:Fin : forall {n} -> Number (Fin (suc n))
  Number:Fin {n} = record {
      Constraint = \ m -> cast (m <= n);
      fromNat = \ m {{p}} -> fromN m n p
    }
