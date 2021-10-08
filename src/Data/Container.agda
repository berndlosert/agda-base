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
  constructor container
  field
    Shape : Set
    position : Shape -> Set

open Container public

Id : Container
Id .Shape = Unit
Id .position = const Unit

Const : Set -> Container
Const a .Shape = a
Const a .position = const Void

Sum : Container -> Container -> Container
Sum c d .Shape = Either (Shape c) (Shape d)
Sum c d .position = either (position c) (position d)

Product : Container -> Container -> Container
Product c d .Shape = Pair (Shape c) (Shape d)
Product c d .position = \ where
  (s , t) -> Either (position c s) (position d t)

-------------------------------------------------------------------------------
-- Extension
-------------------------------------------------------------------------------

record Extension (c : Container) (a : Set) : Set where
  constructor extension
  field
    shape : Shape c
    position : position c shape -> a

open Extension public

instance
  Functor-Extension : {c : Container} -> Functor (Extension c)
  Functor-Extension .map f (extension s p) = extension s (f <<< p)
