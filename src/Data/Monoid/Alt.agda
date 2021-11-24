module Data.Monoid.Alt where

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
    f : Set -> Set

-------------------------------------------------------------------------------
-- Alt
-------------------------------------------------------------------------------

record Alt (f : Set -> Set) (a : Set) : Set where
  constructor anAlt
  field getAlt : f a

open Alt public

instance
  Semigroup-Alt : {{Alternative f}} -> Semigroup (Alt f a)
  Semigroup-Alt ._<>_ x y = anAlt (getAlt x <|> getAlt y)

  Monoid-Alt : {{Alternative f}} -> Monoid (Alt f a)
  Monoid-Alt .mempty = anAlt azero
