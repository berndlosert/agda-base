{-# OPTIONS --type-in-type #-}

module Data.Foldable1 where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Constraint.Nonempty
open import Data.Foldable

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Data.Constraint.Nonempty public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set
    f : Set -> Set

-------------------------------------------------------------------------------
-- IsFoldable1
-------------------------------------------------------------------------------

record IsFoldable1 s a : Set where
  field
    overlap {{IsFoldable-super}} : IsFoldable s a
    overlap {{NonemptyConstraint-super}} : NonemptyConstraint s

  foldMap1 : {{_ : Semigroup b}}
    -> (a -> b) -> (xs : s) {{_ : Nonempty xs}} -> b
  foldMap1 f s = fromJust (foldMap (Just <<< f) s) {{believeMe}}

  fold1 : {{_ : Semigroup a}} (xs : s) {{_ : Nonempty xs}} -> a
  fold1 s = fromJust (foldMap Just s) {{believeMe}}

  foldr1 : (a -> a -> a) -> (xs : s) {{_ : Nonempty xs}} -> a
  foldr1 f s = fromJust (foldr g Nothing s) {{believeMe}}
    where
      g : a -> Maybe a -> Maybe a
      g x Nothing = Just x
      g x (Just y) = Just (f x y)

  foldl1 : (a -> a -> a) -> (xs : s) {{_ : Nonempty xs}} -> a
  foldl1 f s = fromJust (foldl g Nothing s) {{believeMe}}
    where
      g : Maybe a -> a -> Maybe a
      g Nothing x = Just x
      g (Just x) y = Just (f x y)

  module _ {{_ : Ord a}} where

    minimum : (xs : s) {{_ : Nonempty xs}} -> a
    minimum = foldr1 min

    maximum : (xs : s) {{_ : Nonempty xs}} -> a
    maximum = foldr1 max

open IsFoldable1 {{...}} public

-------------------------------------------------------------------------------
-- Foldable1
-------------------------------------------------------------------------------

Foldable1 : (Set -> Set) -> Set
Foldable1 t = forall {a} -> IsFoldable1 (t a) a

instance
  Foldable1-Maybe : Foldable1 Maybe
  Foldable1-Maybe .IsFoldable-super = Foldable-Maybe
  Foldable1-Maybe .NonemptyConstraint-super = NonemptyConstraint-Maybe
