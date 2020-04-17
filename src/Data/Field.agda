{-# OPTIONS --type-in-type #-}

module Data.Field where

open import Data.Ring
open import Data.Semiring

record Field (A : Set) : Set where
  infixr 7 _/_
  field
    overlap {{super}} : Ring A
    _/_ : (x y : A) -> {_ : Nonzero y} -> A

open Field {{...}} public
