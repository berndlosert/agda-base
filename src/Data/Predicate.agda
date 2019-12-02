{-# OPTIONS --type-in-type #-}

module Data.Predicate where

open import Control.Category
open import Data.Bool
open import Data.Functor

-- A Predicate X is a Bool-valued predicate on X.
Predicate : Set -> Set
Predicate X = X -> Bool

-- Predicate is a functor.
instance
  Functor:Predicate : Functor (Op Sets) Sets Predicate
  Functor:Predicate .map f p = f >>> p
