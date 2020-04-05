{-# OPTIONS --type-in-type #-}

module Data.Ring where

open import Data.Semiring public
open import Data.Unit using (Unit; unit)

private variable A B : Set

record Ring (A : Set) : Set where
  infixr 6 _-_
  field
    overlap {{super}} : Semiring A
    -_ : A -> A
    _-_ : A -> A -> A

open Ring {{...}} public

instance
  ringUnit : Ring Unit
  ringUnit .-_ _ = unit
  ringUnit ._-_ _ _ = unit

  ringFunction : {{_ : Ring B}} -> Ring (A -> B)
  ringFunction .-_ f x = - (f x)
  ringFunction ._-_ f g x = f x - g x
