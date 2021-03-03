{-# OPTIONS --type-in-type #-}

module Data.Filtrable where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Set
    f t : Set -> Set

-------------------------------------------------------------------------------
-- Filtrable
-------------------------------------------------------------------------------

record Filtrable (t : Set -> Set) : Set where
  field
    filter : (a -> Bool) -> t a -> t a
    filterA : {{_ : Traversable t}} {{_ : Applicative f}}
      -> (a -> f Bool) -> t a -> f (t a)
    mapMaybe : (a -> Maybe b) -> t a -> t b
    mapMaybeA : {{_ : Traversable t}} {{_ : Applicative f}}
      -> (a -> f (Maybe b)) -> t a -> f (t b)
    mapEither : (a -> Either b c) -> t a -> t b * t c
    mapEitherA : {{_ : Traversable t}} {{_ : Applicative f}}
      -> (a -> f (Either b c)) -> t a -> f (t b * t c)

  partition : (a -> Bool) -> t a -> t a * t a
  partition p xs = (filter p xs , filter (not <<< p) xs)

  catMaybes : t (Maybe a) -> t a
  catMaybes = mapMaybe id

  partitionEithers : t (Either a b) -> t a * t b
  partitionEithers = mapEither id

open Filtrable {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Filtrable-Maybe : Filtrable Maybe
  Filtrable-Maybe .filter p =
    maybe Nothing (\ x -> bool (p x) Nothing (Just x))
