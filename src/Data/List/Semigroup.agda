{-# OPTIONS --type-in-type #-}

module Data.List.Semigroup where

-- List X is a semigroup for any X.

open import Data.List.Base
open import Data.Semigroup public

instance
  Semigroup:List : {X : Set} -> Semigroup (List X)
  Semigroup:List = Semigroup: _++_
