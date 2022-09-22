module Control.Category where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Set

-------------------------------------------------------------------------------
-- Category
-------------------------------------------------------------------------------

record Category {k : Set} (p : k -> k -> Set) : Set where
  field
    compose : {a b c : k} -> p b c -> p a b -> p a c
    identity : {a : k} -> p a a

  infixr 9 _andThen_
  _andThen_ : {a b c : k} -> p a b -> p b c -> p a c
  _andThen_ = flip compose

open Category {{...}} public

instance
  Category-Function : Category Function
  Category-Function .compose = _<<<_
  Category-Function .identity = id