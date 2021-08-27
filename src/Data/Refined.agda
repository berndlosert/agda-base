{-# OPTIONS --type-in-type #-}

module Data.Refined where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Float as Float using ()

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a l r p : Type

-------------------------------------------------------------------------------
-- Validation
-------------------------------------------------------------------------------

record Validation (p a : Type) : Type where
  field
    validate : (q : Type) -> {{q === p}} -> a -> Bool

  Validate : (q : Type) -> {{q === p}} -> a -> Set
  Validate q = Assert <<< validate q

open Validation {{...}} public

data Not (p : Type) : Type where
data Or (l r : Type) : Type where
data And (l r : Type) : Type where
data Positive : Type where
data Nonempty : Type where

instance
  Validation-Not : {{Validation p a}} -> Validation (Not p) a
  Validation-Not {p = p} .validate _ x = not (validate p x)

  Validation-Or : {{Validation l a}} -> {{Validation r a}}
    -> Validation (Or l r) a
  Validation-Or {l = l} {r = r} .validate _ x = validate l x || validate r x

  Validation-And : {{Validation l a}} -> {{Validation r a}}
    -> Validation (And l r) a
  Validation-And {l = l} {r = r} .validate _ x = validate l x && validate r x

  Validation-Positive-Nat : Validation Positive Nat
  Validation-Positive-Nat .validate _ 0 = False
  Validation-Positive-Nat .validate _ _ = True

  Validation-Positive-Int : Validation Positive Int
  Validation-Positive-Int .validate _ (Pos 0) = False
  Validation-Positive-Int .validate _ _ = True

  Validation-Positive-Float : Validation Positive Float
  Validation-Positive-Float .validate _ x = x > 0.0

  Validation-Nonempty-String : Validation Nonempty String
  Validation-Nonempty-String .validate _ "" = False
  Validation-Nonempty-String .validate _ _ = True

  Validation-Nonempty-Maybe : Validation Nonempty (Maybe a)
  Validation-Nonempty-Maybe .validate _ Nothing = False
  Validation-Nonempty-Maybe .validate _ _ = True

  Validation-Nonempty-List : Validation Nonempty (List a)
  Validation-Nonempty-List .validate _ [] = False
  Validation-Nonempty-List .validate _ _ = True

-------------------------------------------------------------------------------
-- Refined
-------------------------------------------------------------------------------

record Refined (p a : Set) {{_ : Validation p a}} : Set where
  constructor Refined:
  field
    unrefine : a
    {validation} : Validate p unrefine

open Refined public
