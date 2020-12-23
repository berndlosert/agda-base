{-# OPTIONS --type-in-type #-}

module Data.Foldable where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Alternative
open import Data.Constraint.Nonempty
open import Data.Monoid.All
open import Data.Monoid.Any

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Data.Monoid.All public
open Data.Monoid.Any public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set
    f m t : Set -> Set

-------------------------------------------------------------------------------
-- Foldable
-------------------------------------------------------------------------------

record Foldable (t : Set -> Set) : Set where
  field foldr : (a -> b -> b) -> b -> t a -> b

  foldMap : {{_ : Monoid b}} -> (a -> b) -> t a -> b
  foldMap f = foldr (_<>_ <<< f) neutral

  fold : {{_ : Monoid a}} -> t a -> a
  fold = foldMap id

  foldl : (b -> a -> b) -> b -> t a -> b
  foldl f b as = foldr (_>>>_ <<< flip f) id as b

  foldrM : {{_ : Monad m}} -> (a -> b -> m b) -> b -> t a -> m b
  foldrM f b as = let g k a b' = f a b' >>= k in
    foldl g return as b

  foldlM : {{_ : Monad m}} -> (b -> a -> m b) -> b -> t a -> m b
  foldlM f b as = let g a k b' = f b' a >>= k in
    foldr g return as b

  toList : t a -> List a
  toList = foldMap [_]

  length : t a -> Nat
  length = foldr (const Suc) 0

  find : (a -> Bool) -> t a -> Maybe a
  find p = either Just (const Nothing) <<<
    foldlM (\ _ a ->  if p a then Left a else Right unit) unit

  any : (a -> Bool) -> t a -> Bool
  any p xs = maybe False (const True) (find p xs)

  all : (a -> Bool) -> t a -> Bool
  all p = not <<< any (not <<< p)

  or : t Bool -> Bool
  or = any (_== True)

  and : t Bool -> Bool
  and = all (_== True)

  null : t a -> Bool
  null = foldr (\ _ _ -> False) True

  sum : {{ _ : Additive a}} -> t a -> a
  sum = foldr _+_ zero

  product : {{ _ : Multiplicative a}} -> t a -> a
  product = foldr _*_ one

  module _ {{_ : Eq a}} where

    elem : a -> t a -> Bool
    elem = any <<< _==_

    notElem : a -> t a -> Bool
    notElem a s = not (elem a s)

  module _ {{_ : Applicative f}} where

    traverse! : (a -> f b) -> t a -> f Unit
    traverse! f = foldr (_*>_ <<< f) (pure unit)

    for! : t a -> (a -> f b) -> f Unit
    for! = flip traverse!

  module _ {{_ : NonemptyConstraint (t a)}} where

    foldMap1 : {{_ : Semigroup b}}
      -> (a -> b) -> (xs : t a) {{_ : IsNonempty xs}} -> b
    foldMap1 f s = fromJust (foldMap (Just <<< f) s) {{believeMe}}

    fold1 : {{_ : Semigroup a}} (xs : t a) {{_ : IsNonempty xs}} -> a
    fold1 s = fromJust (foldMap Just s) {{believeMe}}

    foldr1 : (a -> a -> a) -> (xs : t a) {{_ : IsNonempty xs}} -> a
    foldr1 f s = fromJust (foldr g Nothing s) {{believeMe}}
      where
        g : a -> Maybe a -> Maybe a
        g x Nothing = Just x
        g x (Just y) = Just (f x y)

    foldl1 : (a -> a -> a) -> (xs : t a) {{_ : IsNonempty xs}} -> a
    foldl1 f s = fromJust (foldl g Nothing s) {{believeMe}}
      where
        g : Maybe a -> a -> Maybe a
        g Nothing x = Just x
        g (Just x) y = Just (f x y)

    module _ {{_ : Ord a}} where

      minimum : (xs : t a) {{_ : IsNonempty xs}} -> a
      minimum = foldr1 min

      maximum : (xs : t a) {{_ : IsNonempty xs}} -> a
      maximum = foldr1 max

  module _ {{_ : Applicative f}} where

    sequence! : t (f a) -> f Unit
    sequence! = traverse! id

  module _ {{_ : Alternative f}} where

    asum : t (f a) -> f a
    asum = foldr _<|>_ empty

open Foldable {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Foldable-Maybe : Foldable Maybe
  Foldable-Maybe .foldr f b = maybe b (flip f b)

  Foldable-List : Foldable List
  Foldable-List .foldr f b = listrec b (\ x _ y -> f x y)
