module Properties.Semigroup where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
      a b : Type

-------------------------------------------------------------------------------
-- Semigroup Properties
-------------------------------------------------------------------------------

module _ {{_ : Semigroup a}} {{_ : Eq a}}  where
  associativity : a -> a -> a -> Bool
  associativity x y z = x <> (y <> z) == (x <> y) <> z

  preservesOperation : {{Semigroup b}} -> {{Eq b}}
    -> (a -> b) -> a -> a -> Bool
  preservesOperation f x y = f (x <> y) == f x <> f y