{-# OPTIONS --type-in-type #-}

module Notation.Append where

record Append (X Y Z : Set) : Set where
  constructor Append:
  infixr 25 _++_
  field _++_ : X -> Y -> Z

open Append {{...}} public
