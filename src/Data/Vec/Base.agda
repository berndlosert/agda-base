{-# OPTIONS --type-in-type #-}

module Data.Vec.Base where

-- The type Vec X n is the type of lists of Xs of length n.

open import Data.Nat

data Vec (X : Set) : Nat -> Set where
  [] : Vec X 0
  _::_ : forall {n} -> X -> Vec X n -> Vec X (suc n)
