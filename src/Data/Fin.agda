{-# OPTIONS --type-in-type #-}

module Data.Fin where

open import Prelude
  hiding (zero)

private variable n : Nat

data Fin : Nat -> Set where
  zero : Fin (suc n)
  suc : Fin n -> Fin (suc n)

-- Convert a Fin n into a Nat.
toNat : Fin n -> Nat
toNat zero = 0
toNat (suc n) = suc (toNat n)

-- The Number:Fin instance allows us to write Fin n values using natural
-- number literals.
--instance
--  Number:Fin : forall {n} -> Number (Fin (suc n))
--  Number:Fin {n} = record {
--      Constraint = λ m -> Assert (m <= n);
--      fromNat = λ m {{p}} -> go m n {p}
--    }
--    where
--      go : forall m n -> {_ : Assert (m <= n)} -> Fin (suc n)
--      go zero _ = zero
--      go (suc m) (suc n) {p} = suc (go m n {p})
