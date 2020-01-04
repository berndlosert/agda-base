{-# OPTIONS --type-in-type #-}

module Data.Fin where

open import Data.Fin.Base public
  hiding (module Fin)

module Fin where

  -- Convert a Fin n into a Nat.
  
  toNat : {n : Nat} -> Fin n -> Nat
  toNat zero = zero
  toNat (suc n) = suc (toNat n)
  
  -- The Number:Fin instance allows us to write Fin n values using natural
  -- number literals.
  
  open import Data.Eq
  open import Data.Ord
  open import Notation.Number

  Number:Fin : forall {n} -> Number (Fin (suc n))
  Number:Fin {n} = record {
      Constraint = \ m -> Constraint (m <= n);
      fromNat = \ m {{p}} -> go m n {p}
    }
    where
      go : forall m n -> {_ : Constraint (m <= n)} -> Fin (suc n)
      go zero _ = zero
      go (suc m) (suc n) {p} = suc (go m n {p})

open Fin public
  using (Number:Fin)
