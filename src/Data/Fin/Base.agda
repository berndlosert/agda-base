{-# OPTIONS --type-in-type #-}

module Data.Fin.Base where

open import Data.Nat public

-- The type Fin (suc n) has n + 1 inhabitants, namely 0, 1, ..., n. Note that
-- Fin 0 is effectively the same as Void.

data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc : {n : Nat} -> Fin n -> Fin (suc n)
