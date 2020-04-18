{-# OPTIONS --type-in-type #-}

module Data.Ring where

open import Data.Ord
open import Data.Monoid
open import Data.Semiring
open import Prim

private variable A B : Set

record Ring (A : Set) : Set where
  infixr 6 _-_
  field
    overlap {{super}} : Semiring A
    -_ : A -> A
    _-_ : A -> A -> A

  abs : {{_ : Ord A}} -> A -> A
  abs a = if a < zero then - a else a

open Ring {{...}} public
