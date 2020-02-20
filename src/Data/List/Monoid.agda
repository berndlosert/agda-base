{-# OPTIONS --type-in-type #-}

module Data.List.Monoid where

open import Data.List.Base
open import Data.List.Semigroup
open import Data.Monoid public

instance
  Monoid:List : {X : Set} -> Monoid (List X)
  Monoid:List = Monoid: []
