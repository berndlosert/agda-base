{-# OPTIONS --type-in-type #-}

module Data.Division where

open import Data.Ring using (Ring)

record Division (A : Set) : Set where
  infixr 7 _/_ _%_
  field
    overlap {{superRing}} : Ring A
    Nonzero : A -> Set
    _/_ : (x y : A) -> {_ : Nonzero y} -> A
    _%_ : (x y : A) -> {_ : Nonzero y} -> A

open Division {{...}} public
