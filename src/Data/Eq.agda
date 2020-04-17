{-# OPTIONS --type-in-type #-}

module Data.Eq where

open import Prim

record Eq (A : Set) : Set where
  infix 4 _==_
  field _==_ : A -> A -> Bool

  infix 4 _/=_
  _/=_ : A -> A -> Bool
  x /= y = if x == y then false else true

open Eq {{...}} public
