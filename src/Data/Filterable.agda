{-# OPTIONS --type-in-type #-}

module Data.Filterable where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable
open import Data.Traversable
open import Data.Profunctor.Strong

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

open Filterable {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Filterable-Maybe : Filterable Maybe
  Filterable-Maybe .filter p = maybe Nothing \ x ->
    bool (p x) Nothing (Just x)
  Filterable-Maybe .filterA p = maybe (| Nothing |) \ x ->
    (| bool (p x) (| Nothing |) (| (Just x) |) |)
  Filterable-Maybe .mapMaybe f = maybe Nothing f
  Filterable-Maybe .mapMaybeA f = maybe (| Nothing |) f
  Filterable-Maybe .mapEither f = maybe (Nothing , Nothing) \ x ->
    either (Just &&& const Nothing) (const Nothing &&& Just) (f x)
  Filterable-Maybe .mapEitherA f = maybe (| (Nothing , Nothing) |) \ x ->
    (| (either (Just &&& const Nothing) (const Nothing &&& Just)) (f x) |)

  Filterable-List : Filterable List
  Filterable-List .filter p = flip foldr [] \ where
    x xs -> bool (p x) xs (x :: xs)
  Filterable-List .filterA p = flip (foldr {{Foldable-List}}) (| [] |) \ where
    x xs -> (| bool (p x) xs (| (x ::_) xs |) |)
  Filterable-List .mapMaybe f = flip foldr [] \ where
    x xs -> maybe xs (_:: xs) (f x)
  Filterable-List .mapMaybeA f = flip (foldr {{Foldable-List}}) (| [] |) \ where
    x xs -> (| maybe xs (| (flip _::_) xs |) (f x) |)
  Filterable-List .mapEither f = flip foldr ([] , []) \ where
    x (ls , rs) -> either (_:: ls &&& const rs) (const ls &&& _:: rs) (f x)
  Filterable-List .mapEitherA f = undefined
  --Filterable-List .mapEitherA f = flip foldr (| ([] , []) |) \ where
  --  x (ls , rs) -> (| (either (_:: ls &&& const rs) (const ls &&& _:: rs)) (f x) |)
