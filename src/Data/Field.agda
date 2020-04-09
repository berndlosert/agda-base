{-# OPTIONS --type-in-type #-}

module Data.Field where

open import Data.Ring public

record Field (A : Set) : Set where
  infixr 7 _/_
  field
    overlap {{super}} : Ring A
    Nonzero : A -> Set
    _/_ : (x y : A) -> {_ : Nonzero y} -> A

open Field {{...}} public
