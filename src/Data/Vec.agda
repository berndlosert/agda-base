{-# OPTIONS --type-in-type #-}

module Data.Vec where

open import Data.Vec.Base public
  hiding (module Vec)

module Vec where

  -- Append two vectors.

  open import Data.Bool
  open import Data.Nat
  open import Data.Ord
  open import Notation.Add
  open import Notation.Append

  instance
    Append:Vec : forall {m n X} -> Append (Vec X m) (Vec X n) (Vec X (m + n))
    Append:Vec ._++_ [] ys = ys
    Append:Vec ._++_ (x :: xs) ys = x :: xs ++ ys

  -- Split a vector into two parts.

  open import Data.Tuple
  open import Notation.Mul

  splitAt : forall m {n X} -> Vec X (m + n) -> Vec X m * Vec X n
  splitAt zero xs = ([] , xs)
  splitAt (suc k) (x :: xs) with (splitAt k xs)
  ... | (tk , dr) = (x :: tk , dr)

open Vec using (Append:Vec)
