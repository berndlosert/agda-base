{-# OPTIONS --type-in-type #-}

module Data.Field where

open import Data.Eq using (Eq)
open import Data.Ring using (Ring)
open import Data.Semiring using (Nonzero)

record Field (A : Set) : Set where
  infixr 7 _/_
  field
    overlap {{superRing}} : Ring A
    overlap {{superEq}} : Eq A
    _/_ : (x y : A) -> {_ : Nonzero y} -> A

open Field {{...}} public
