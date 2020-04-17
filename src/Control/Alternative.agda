{-# OPTIONS --type-in-type #-}

module Control.Alternative where

open import Control.Applicative

private variable A : Set

record Alternative (F : Set -> Set) : Set where
  infixl 3 _<|>_
  field
    overlap {{super}} : Applicative F
    _<|>_ : F A -> F A -> F A
    empty : F A

open Alternative {{...}} public
