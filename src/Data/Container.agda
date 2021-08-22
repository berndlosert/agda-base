{-# OPTIONS --type-in-type #-}

module Data.Container where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Container
-------------------------------------------------------------------------------

record Container : Type where
  constructor Container:
  field
    Shape : Type
    Position : Shape -> Type

open Container public

-------------------------------------------------------------------------------
-- Extension
-------------------------------------------------------------------------------

record Extension (c : Container) (a : Type) : Type where
  constructor Extension:
  field
    shape : Shape c
    position : Position c shape -> a

open Extension public

instance
  Functor-Extension : {c : Container} -> Functor (Extension c)
  Functor-Extension .map f (Extension: s p) = Extension: s (f <<< p)
