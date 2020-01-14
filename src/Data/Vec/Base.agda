{-# OPTIONS --type-in-type #-}

module Data.Vec.Base where

-- The type Vec X n is the type of lists of Xs of length n.

open import Data.Nat public

data Vec (X : Set) : Nat -> Set where
  [] : Vec X 0
  _::_ : forall {n} -> X -> Vec X n -> Vec X (suc n)

-- Append two vectors.

open import Notation.Append public

instance
  Append:Vec : forall {m n X} -> Append (Vec X m) (Vec X n) (Vec X (m + n))
  Append:Vec ._++_ [] ys = ys
  Append:Vec ._++_ (x :: xs) ys = x :: xs ++ ys
