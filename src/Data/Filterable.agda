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
    a b c : Type
    f t : Type -> Type

-------------------------------------------------------------------------------
-- Filterable
-------------------------------------------------------------------------------

record Filterable (t : Type -> Type) : Type where
  field
    mapMaybe : (a -> Maybe b) -> t a -> t b

  mapEither : (a -> Either b c) -> t a -> t b * t c
  mapEither t = (|
      _,_
      (mapMaybe (either Just (pure Nothing) <<< t))
      (mapMaybe (either (pure Nothing) Just <<< t))
    |)

  filter : (a -> Bool) -> t a -> t a
  filter p = mapMaybe (\ x -> if p x then Just x else Nothing)

  partition : (a -> Bool) -> t a -> t a * t a
  partition p xs = (filter p xs , filter (not <<< p) xs)

  catMaybes : t (Maybe a) -> t a
  catMaybes = mapMaybe id

  partitionEithers : t (Either a b) -> t a * t b
  partitionEithers = mapEither id

  module _ {{_ : Traversable t}} where

    mapMaybeA : {{_ : Applicative f}} -> (a -> f (Maybe b)) -> t a -> f (t b)
    mapMaybeA f xs = (| catMaybes (traverse f xs) |)

    filterA : {{_ : Applicative f}} -> (a -> f Bool) -> t a -> f (t a)
    filterA p =
      mapMaybeA (\ x -> (| bool (| Nothing |) (| (Just x) |) (p x) |))

    mapEitherA : {{_ : Applicative f}}
        -> (a -> f (Either b c)) -> t a -> f (t b * t c)
    mapEitherA f = (|
        (\ x y -> (| _,_ x y |))
        (mapMaybeA (map (either Just (pure Nothing)) <<< f))
        (mapMaybeA (map (either (pure Nothing) Just) <<< f))
      |)

open Filterable {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Filterable-Maybe : Filterable Maybe
  Filterable-Maybe .mapMaybe = _=<<_

  Filterable-List : Filterable List
  Filterable-List .mapMaybe f = foldr (maybe id (_::_) <<< f) []
