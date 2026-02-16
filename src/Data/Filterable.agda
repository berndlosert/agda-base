module Data.Filterable where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Monoid.Foldable
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
  field mapMaybe : (a -> Maybe b) -> t a -> t b

  mapEither : (a -> Either b c) -> t a -> Tuple (t b) (t c)
  mapEither t =
    let
      l = mapMaybe (either just (pure nothing) <<< t)
      r = mapMaybe (either (pure nothing) just <<< t)
    in
      (| l , r |)

  filter : (a -> Bool) -> t a -> t a
  filter p = mapMaybe \ x -> if p x then just x else nothing

  partition : (a -> Bool) -> t a -> Tuple (t a) (t a)
  partition p xs = (filter p xs , filter (not <<< p) xs)

  catMaybes : t (Maybe a) -> t a
  catMaybes = mapMaybe id

  partitionEithers : t (Either a b) -> Tuple (t a) (t b)
  partitionEithers = mapEither id

  lefts : t (Either a b) -> t a
  lefts = mapMaybe (either just (const nothing))

  rights : t (Either a b) -> t b
  rights = mapMaybe (either (const nothing) just)

open Filterable {{...}} public

-------------------------------------------------------------------------------
-- Witherable
-------------------------------------------------------------------------------

record Witherable (t : Type -> Type) : Type where
  field
    overlap {{Filterable-super}} : Filterable t
    overlap {{Traversable-super}} : Traversable t

  module _ {{_ : Applicative f}} where
    mapMaybeA : (a -> f (Maybe b)) -> t a -> f (t b)
    mapMaybeA f xs = (| catMaybes (traverse f xs) |)

    filterA : (a -> f Bool) -> t a -> f (t a)
    filterA p =
      mapMaybeA \ x -> (| if p x then (| (just x) |) else (| nothing |) |)

    mapEitherA : (a -> f (Either b c)) -> t a -> f (Tuple (t b) (t c))
    mapEitherA f =
      let
        l = mapMaybeA (map (either just (pure nothing)) <<< f)
        r = mapMaybeA (map (either (pure nothing) just) <<< f)
      in
        (| (\ x y -> (| x , y |)) l r |)

open Witherable {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Witherable-inst : {{Filterable t}} -> {{Traversable t}} -> Witherable t
  Witherable-inst = record {}

  Filterable-Maybe : Filterable Maybe
  Filterable-Maybe .mapMaybe = flip _>>=_

  Filterable-Either : {{Monoid a}} -> Filterable (Either a)
  Filterable-Either .mapMaybe f = \where
    (left x) -> left x
    (right x) -> maybe (left mempty) right (f x)

  Filterable-List : Filterable List
  Filterable-List .mapMaybe f xs = foldr (maybe id (_::_) <<< f) [] xs
