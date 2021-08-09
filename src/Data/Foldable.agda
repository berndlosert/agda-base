{-# OPTIONS --type-in-type #-}

module Data.Foldable where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Alternative
open import Data.Refined

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type
    f m t : Type -> Type

-------------------------------------------------------------------------------
-- Step (for foldl')
-------------------------------------------------------------------------------

data Step (a : Type) : Type where
  Done : a -> Step a
  Continue : a -> Step a

-------------------------------------------------------------------------------
-- Foldable
-------------------------------------------------------------------------------

record Foldable (t : Type -> Type) : Type where
  field foldr : (a -> b -> b) -> b -> t a -> b

  foldMap : {{Monoid b}} -> (a -> b) -> t a -> b
  foldMap f = foldr (_<>_ <<< f) neutral

  fold : {{Monoid a}} -> t a -> a
  fold = foldMap id

  foldl : (b -> a -> b) -> b -> t a -> b
  foldl {b} {a} f = flip $ foldr go id
    where
      go : a -> (b -> b) -> b -> b
      go x k z = k $! f z x

  -- Short-circuiting foldl.
  foldl' : (b -> a -> Step b) -> b -> t a -> b
  foldl' {b} {a} f = flip $ foldr go id
    where
      go : a -> (b -> b) -> b -> b
      go x k z = case f z x of \ where
        (Done result) -> result
        (Continue accum) -> k accum

  foldlM : {{Monad m}} -> (b -> a -> m b) -> b -> t a -> m b
  foldlM {m} {b} {a} f = flip $ foldr go pure
    where
      go : a -> (b -> m b) -> b -> m b
      go x k z = f z x >>= k

  foldrM : {{Monad m}} -> (a -> b -> m b) -> b -> t a -> m b
  foldrM f z xs = let g k y z' = f y z' >>= k in
    foldl g pure xs z

  toList : t a -> List a
  toList = foldMap (_:: [])

  concat : t (List a) -> List a
  concat = fold

  concatMap : (a -> List b) -> t a -> List b
  concatMap = foldMap

  length : t a -> Nat
  length = foldr (const Suc) 0

  find : (a -> Bool) -> t a -> Maybe a
  find p = foldl' (\ _ x ->  if p x then Done (Just x) else Continue Nothing) Nothing

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

  sum : {{Additive a}} -> t a -> a
  sum = foldl _+_ zero

  product : {{Multiplicative a}} -> t a -> a
  product = foldl _*_ one

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

  module _ {{_ : Validation Nonempty (t a)}} where

    foldMap1 : {{Semigroup b}}
      -> (a -> b) -> (xs : t a) -> {{Validate {Nonempty} xs}} -> b
    foldMap1 f s = fromJust (foldMap (Just <<< f) s) {{trustMe}}

    fold1 : {{Semigroup a}} -> (xs : t a) -> {{Validate {Nonempty} xs}} -> a
    fold1 s = fromJust (foldMap Just s) {{trustMe}}

    foldr1 : (a -> a -> a) -> (xs : t a) -> {{Validate {Nonempty} xs}} -> a
    foldr1 f s = fromJust (foldr g Nothing s) {{trustMe}}
      where
        g : a -> Maybe a -> Maybe a
        g x Nothing = Just x
        g x (Just y) = Just (f x y)

    foldl1 : (a -> a -> a) -> (xs : t a) -> {{Validate {Nonempty} xs}} -> a
    foldl1 f s = fromJust (foldl g Nothing s) {{trustMe}}
      where
        g : Maybe a -> a -> Maybe a
        g Nothing x = Just x
        g (Just x) y = Just (f x y)

    module _ {{_ : Ord a}} where

      minimum : (xs : t a) -> {{Validate {Nonempty} xs}} -> a
      minimum = foldr1 min

      maximum : (xs : t a) -> {{Validate {Nonempty} xs}} -> a
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
  Foldable-Maybe .foldr f z = maybe z (flip f z)

  Foldable-List : Foldable List
  Foldable-List .foldr f z = \ where
    [] -> z
    (x :: xs) -> f x (foldr f z xs)
