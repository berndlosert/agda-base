{-# OPTIONS --type-in-type #-}

module Data.Foldable where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Alternative

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set
    f m t : Set -> Set

-------------------------------------------------------------------------------
-- Step (for foldl')
-------------------------------------------------------------------------------

data Step (a : Set) : Set where
  Done : a -> Step a
  Continue : a -> Step a

-------------------------------------------------------------------------------
-- Foldable
-------------------------------------------------------------------------------

record Foldable (t : Set -> Set) : Set where
  field foldr : (a -> b -> b) -> b -> t a -> b

  foldMap : {{Monoid b}} -> (a -> b) -> t a -> b
  foldMap {b} {a} f = foldr go neutral
    where
      go : a -> b -> b
      go x z = f x <> z

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
  foldrM {m} {a} {b} f = flip $ foldl go pure
    where
      go : (b -> m b) -> a -> b -> m b
      go k x z = f x z >>= k

  toList : t a -> List a
  toList = foldMap (_:: [])

  concat : t (List a) -> List a
  concat = fold

  concatMap : (a -> List b) -> t a -> List b
  concatMap = foldMap

  length : t a -> Nat
  length = foldr (const Suc) Zero

  find : (a -> Bool) -> t a -> Maybe a
  find {a} p = foldl' go Nothing
    where
      go : Maybe a -> a -> Step (Maybe a)
      go _ x = if p x then Done (Just x) else Continue Nothing

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

  module _ {{fn : FromNat a}} where

    sum : {{Add a}} -> {{FromNatConstraint {{fn}} 0}} -> t a -> a
    sum = foldl _+_ 0

    product : {{Mul a}} -> {{FromNatConstraint {{fn}} 1}} -> t a -> a
    product = foldl _*_ 1

  module _ {{_ : Eq a}} where

    elem : a -> t a -> Bool
    elem = any <<< _==_

    notElem : a -> t a -> Bool
    notElem a s = not (elem a s)

  minimumBy : (a -> a -> Ordering) -> t a -> Maybe a
  minimumBy {a} cmp = foldl min' Nothing
    where
      min' : Maybe a -> a -> Maybe a
      min' Nothing x = Just x
      min' (Just x) y = Just (if cmp x y == LT then x else y)

  maximumBy : (a -> a -> Ordering) -> t a -> Maybe a
  maximumBy {a} cmp = foldl max' Nothing
    where
      max' : Maybe a -> a -> Maybe a
      max' Nothing x = Just x
      max' (Just x) y = Just (if cmp x y == GT then x else y)

  module _ {{_ : Ord a}} where

    minimum : t a -> Maybe a
    minimum = minimumBy compare

    maximum : t a -> Maybe a
    maximum = maximumBy compare

  module _ {{_ : Applicative f}} where

    traverse! : (a -> f b) -> t a -> f Unit
    traverse! f = foldr (_*>_ <<< f) (pure unit)

    for! : t a -> (a -> f b) -> f Unit
    for! = flip traverse!

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

  Foldable-List1 : Foldable List1
  Foldable-List1 .foldr f z (x :| xs) = f x (foldr f z xs)
