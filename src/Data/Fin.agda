{-# OPTIONS --type-in-type #-}

module Data.Fin where

open import Prelude

data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc : {n : Nat} -> Fin n -> Fin (suc n)

-- Convert a Fin n into a Nat.
toNat : {n : Nat} -> Fin n -> Nat
toNat zero = zero
toNat (suc n) = suc (toNat n)

-- The Number:Fin instance allows us to write Fin n values using natural
-- number literals.
instance
  Number:Fin : forall {n} -> Number (Fin (suc n))
  Number:Fin {n} = record {
      Constraint = \ m -> Assert (m <= n);
      fromNat = \ m {{p}} -> go m n {p}
    }
    where
      go : forall m n -> {_ : Assert (m <= n)} -> Fin (suc n)
      go zero _ = zero
      go (suc m) (suc n) {p} = suc (go m n {p})
