{-# OPTIONS --type-in-type #-}

module Data.Maybe.Semigroup where

open import Data.Maybe.Base
open import Data.Semigroup public

instance
  Semigroup:First : forall {X} -> Semigroup (Maybe X)
  Semigroup:First = Semigroup: \ where
    nothing _ -> nothing
    (just x) _ -> just x
