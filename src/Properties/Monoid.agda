module Properties.Monoid where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Data.Monoid using (Monoid; mempty)
open import Data.Semigroup using (_<>_)
open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
      a b : Type

-------------------------------------------------------------------------------
-- Monoid Properties
-------------------------------------------------------------------------------

module _ {{_ : Monoid a}} {{_ : Eq a}} where

  leftIdentity : a -> Bool
  leftIdentity x = mempty <> x == x

  rightIdentity : a -> Bool
  rightIdentity x = x <> mempty == x

  preservesMempty : {{Monoid b}} -> {{Eq b}}
    -> (a -> b) -> Bool
  preservesMempty f = f mempty == mempty