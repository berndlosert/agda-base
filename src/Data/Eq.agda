{-# OPTIONS --type-in-type #-}

module Data.Eq where

-- The type constructor ≡ (also ===) is called propositional equality.

open import Agda.Builtin.Equality public
  renaming (_≡_ to  _===_)

-- Contraint is used for specifying contraints on the arguments of functions.

open import Data.Bool

Constraint : Bool -> Set
Constraint x = x === true

-- We use trustMe to tell Agda that a constraint is satisfied. Use wisely.

open import Agda.Builtin.TrustMe
  renaming (primTrustMe to trustMe)

-- Boolean equality for a type X is specified using an Eq X instance.

record Eq (X : Set) : Set where
  constructor Eq:
  field
    _==_ : X -> X -> Bool

  _/=_ : X -> X -> Bool
  x /= y = not (x == y)

  infix 4 _==_
  infix 4 _/=_

open Eq {{...}} public
