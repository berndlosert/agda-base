{-# OPTIONS --type-in-type #-}

module Notation.Append where

record Append (X : Set) : Set where
  constructor Append:
  infixr 25 _++_
  field _++_ : X → X → X

open Append {{...}} public
