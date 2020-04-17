{-# OPTIONS --type-in-type #-}

module Data.Void where

open import Data.Eq
open import Data.Ord
open import Data.Semigroup
open import Prim

private variable A : Set

absurd : Void -> A
absurd ()

Not : Set -> Set
Not A = A -> Void

instance
  eqVoid : Eq Void
  eqVoid ._==_ = \ ()

  ordVoid : Ord Void
  ordVoid ._<_ = \ ()

  semigroupVoid : Semigroup Void
  semigroupVoid ._<>_ = \ ()
