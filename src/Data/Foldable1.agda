{-# OPTIONS --type-in-type #-}

module Data.Foldable1 where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set
    f : Set -> Set

-------------------------------------------------------------------------------
-- Foldable1
-------------------------------------------------------------------------------

record Foldable1 (t : Set -> Set) : Set where
  field
    overlap {{Foldable-super}} : Foldable t
    overlap {{NonemptyConstraint-super}} : NonemptyConstraint (t a)

  foldMap1 : {{_ : Semigroup b}}
    -> (a -> b) -> (xs : t a) {{_ : Nonempty xs}} -> b
  foldMap1 f s = fromJust (foldMap (Just <<< f) s) {{believeMe}}

  fold1 : {{_ : Semigroup a}} (xs : t a) {{_ : Nonempty xs}} -> a
  fold1 s = fromJust (foldMap Just s) {{believeMe}}

  foldr1 : (a -> a -> a) -> (xs : t a) {{_ : Nonempty xs}} -> a
  foldr1 {a} f s = fromJust (foldr g Nothing s) {{believeMe}}
    where
      g : a -> Maybe a -> Maybe a
      g x Nothing = Just x
      g x (Just y) = Just (f x y)

  foldl1 : (a -> a -> a) -> (xs : t a) {{_ : Nonempty xs}} -> a
  foldl1 {a} f s = fromJust (foldl g Nothing s) {{believeMe}}
    where
      g : Maybe a -> a -> Maybe a
      g Nothing x = Just x
      g (Just x) y = Just (f x y)

  module _ {{_ : Ord a}} where

    minimum : (xs : t a) {{_ : Nonempty xs}} -> a
    minimum = foldr1 min

    maximum : (xs : t a) {{_ : Nonempty xs}} -> a
    maximum = foldr1 max

open Foldable1 {{...}} public

instance
  Foldable1-Maybe : Foldable1 Maybe
  Foldable1-Maybe .NonemptyConstraint-super = NonemptyConstraint-Maybe
  Foldable1-Maybe .Foldable-super = Foldable-Maybe

  Foldable1-List : Foldable1 List
  Foldable1-List .NonemptyConstraint-super = NonemptyConstraint-List
  Foldable1-List .Foldable-super = Foldable-List
