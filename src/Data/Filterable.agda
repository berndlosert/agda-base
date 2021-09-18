{-# OPTIONS --type-in-type #-}

module Data.Filterable where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Set
    f t : Set -> Set

-------------------------------------------------------------------------------
-- Filterable
-------------------------------------------------------------------------------

record Filterable (t : Set -> Set) : Set where
  field
    mapMaybe : (a -> Maybe b) -> t a -> t b

  mapEither : (a -> Either b c) -> t a -> Pair (t b) (t c)
  mapEither t =
    let
      l = mapMaybe (either just (pure nothing) <<< t)
      r = mapMaybe (either (pure nothing) just <<< t)
    in
      (| l , r |)

  filter : (a -> Bool) -> t a -> t a
  filter p = mapMaybe (\ x -> if p x then just x else nothing)

  partition : (a -> Bool) -> t a -> Pair (t a) (t a)
  partition p xs = (filter p xs , filter (not <<< p) xs)

  catMaybes : t (Maybe a) -> t a
  catMaybes = mapMaybe id

  partitionEithers : t (Either a b) -> Pair (t a) (t b)
  partitionEithers = mapEither id

  module _ {{_ : Traversable t}} {{_ : Applicative f}} where

    mapMaybeA : (a -> f (Maybe b)) -> t a -> f (t b)
    mapMaybeA f xs = (| catMaybes (traverse f xs) |)

    filterA : (a -> f Bool) -> t a -> f (t a)
    filterA p =
      mapMaybeA (\ x -> (| bool (| nothing |) (| (just x) |) (p x) |))

    mapEitherA : (a -> f (Either b c)) -> t a -> f (Pair (t b) (t c))
    mapEitherA f = (|
        (\ x y -> (| x , y |))
        (mapMaybeA (map (either just (pure nothing)) <<< f))
        (mapMaybeA (map (either (pure nothing) just) <<< f))
      |)

open Filterable {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Filterable-Maybe : Filterable Maybe
  Filterable-Maybe .mapMaybe = flip _>>=_

  Filterable-List : Filterable List
  Filterable-List .mapMaybe f = foldr (maybe id (_::_) <<< f) []
