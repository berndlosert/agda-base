{-# OPTIONS --type-in-type #-}

module Data.Fin where

open import Data.Nat public

module Base where

  -- The type Fin (suc n) has n + 1 inhabitants, namely 0, 1, ..., n. Note that
  -- Fin 0 is effectively the same as Void.
  
  data Fin : Nat -> Set where
    zero : {n : Nat} -> Fin (suc n)
    suc : {n : Nat} -> Fin n -> Fin (suc n)

open Base public
  hiding (module Fin)

module Fin where

  -- Convert a Fin n into a Nat.
  
  toNat : {n : Nat} -> Fin n -> Nat
  toNat zero = zero
  toNat (suc n) = suc (toNat n)
  
  -- Convert a value m : Nat into a Fin (suc n) assuming m <= n. 

  open import Data.Eq
  
  fromNat : forall m n -> {_ : Constraint (m <= n)} -> Fin (suc n)
  fromNat zero _ = zero
  fromNat (suc m) (suc n) {p} = suc (fromNat m n {p})
  
  -- The Number:Fin instance allows us to write Fin n values using natural
  -- number literals.
  
  open import Notation.Number

  Number:Fin : forall {n} -> Number (Fin (suc n))
  Number:Fin {n} = record {
      Constraint = \ m -> Constraint (m <= n);
      fromNat = \ m {{p}} -> fromNat m n {p}
    }

open Fin public
  using (Number:Fin)
