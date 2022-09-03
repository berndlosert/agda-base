module Data.NonEmpty where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

-------------------------------------------------------------------------------
-- HasNonEmpty
-------------------------------------------------------------------------------

record HasNonEmpty (a : Set) : Set where
  field isNonEmpty : a -> Bool

open HasNonEmpty {{...}} public

instance
  HasNonEmpty-String : HasNonEmpty String
  HasNonEmpty-String .isNonEmpty "" = false
  HasNonEmpty-String .isNonEmpty _ = true

  HasNonEmpty-Maybe : HasNonEmpty (Maybe a)
  HasNonEmpty-Maybe .isNonEmpty = isJust

  HasNonEmpty-List : HasNonEmpty (List a)
  HasNonEmpty-List .isNonEmpty [] = false
  HasNonEmpty-List .isNonEmpty _ = true

-------------------------------------------------------------------------------
-- NonEmpty
-------------------------------------------------------------------------------

data NonEmpty (a : Set) : Set where
  unsafeNonEmpty : a -> NonEmpty a

toNonEmpty : {{HasNonEmpty a}} -> a -> Maybe (NonEmpty a)
toNonEmpty x = if isNonEmpty x then just (unsafeNonEmpty x) else nothing

fromNonEmpty : {{HasNonEmpty a}} -> NonEmpty a -> a
fromNonEmpty (unsafeNonEmpty x) = x

