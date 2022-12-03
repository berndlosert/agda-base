module Control.Category where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (_>>>_; _<<<_; id)

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
  infixr 9 _<<<_
  field
    _<<<_ : {a b c : k} -> p b c -> p a b -> p a c
    id : {a : k} -> p a a

  infixr 9 _>>>_
  _>>>_ : {a b c : k} -> p a b -> p b c -> p a c
  _>>>_ = flip _<<<_

open Category {{...}} public

instance
  Category-Function : Category Function
  Category-Function ._<<<_ = Prelude._<<<_
  Category-Function .id = Prelude.id