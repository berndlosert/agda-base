{-# OPTIONS --type-in-type #-}

module Data.Eq where

open import Data.Bool using (Bool; true; false; not)
open import Data.Unit using (Unit; unit)
open import Data.Void using (Void)

record Eq (A : Set) : Set where
  infix 4 _==_
  field _==_ : A -> A -> Bool

  infix 4 _/=_
  _/=_ : A -> A -> Bool
  x /= y = not (x == y)

open Eq {{...}} public

instance
  eqVoid : Eq Void
  eqVoid ._==_ = \ ()

  eqUnit : Eq Unit
  eqUnit ._==_ unit unit = true

  eqBool : Eq Bool
  eqBool ._==_ = \ where
    true true -> true
    false false -> false
    _ _ -> false
