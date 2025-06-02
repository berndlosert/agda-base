module Properties.Eq where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
      a : Type

-------------------------------------------------------------------------------
-- Eq Properties
-------------------------------------------------------------------------------

module _ {{_ : Eq a}} where

  reflexivity : a -> Bool
  reflexivity x = x == x

  symmetry : a -> a -> Bool
  symmetry x y = (x == y) implies (y == x)

  transitivity : a -> a -> a -> Bool
  transitivity x y z = (x == y && y == z) implies (x == z)

  negation : a -> a -> Bool
  negation x y = (x /= y) == not (x == y)