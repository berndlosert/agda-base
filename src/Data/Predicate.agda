{-# OPTIONS --type-in-type #-}

module Data.Predicate where

open import Prelude

Predicate : Set -> Set
Predicate X = X -> Bool

instance
  Functor:Predicate : Contravariant Predicate
  Functor:Predicate .map f p = f >>> p
