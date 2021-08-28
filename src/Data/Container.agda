{-# OPTIONS --type-in-type #-}

module Data.Container where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Container
-------------------------------------------------------------------------------

record Container : Set where
  constructor Container:
  field
    Shape : Set
    Position : Shape -> Set

open Container public

-------------------------------------------------------------------------------
-- Extension
-------------------------------------------------------------------------------

record Extension (c : Container) (a : Set) : Set where
  constructor Extension:
  field
    shape : Shape c
    position : Position c shape -> a

open Extension public

instance
  Functor-Extension : {c : Container} -> Functor (Extension c)
  Functor-Extension .map f (Extension: s p) = Extension: s (f <<< p)
