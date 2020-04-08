{-# OPTIONS --type-in-type #-}

module Data.Num where

open import Data.Ring public

record Num (A : Set) : Set where
  infixr 7 _/_ _%_
  field
    overlap {{superRing}} : Ring A
    Nonzero : A -> Set
    _/_ : (x y : A) -> {_ : Nonzero y} -> A
    _%_ : (x y : A) -> {_ : Nonzero y} -> A

open Num {{...}} public
