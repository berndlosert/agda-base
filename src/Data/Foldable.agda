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
-- Foldable
-------------------------------------------------------------------------------

record Foldable (t : Set -> Set) : Set where
  field foldr : (a -> b -> b) -> b -> t a -> b

  foldMap : {{Monoid b}} -> (a -> b) -> t a -> b
  foldMap f =
    let step x acc = f x <> acc
    in foldr step mempty

  foldMapBy : (b -> b -> b) -> b -> (a -> b) -> t a -> b
  foldMapBy {b} f z = foldMap {{monoid}}
    where
      instance
        monoid : Monoid b
        monoid .Semigroup-super ._<>_ = f
        monoid .mempty = z

  fold : {{Monoid a}} -> t a -> a
  fold = foldMap id

  foldBy : (a -> a -> a) -> a -> t a -> a
  foldBy step init = foldMapBy step init id

  foldl : (b -> a -> b) -> b -> t a -> b
  foldl step =
    let step' x k acc = k $! step acc x
    in flip $ foldr step' id

  foldlM : {{Monad m}} -> (b -> a -> m b) -> b -> t a -> m b
  foldlM step =
    let step' x k acc = step acc x >>= k
    in flip $ foldr step' pure

  foldrM : {{Monad m}} -> (a -> b -> m b) -> b -> t a -> m b
  foldrM step =
    let step' k x acc = step x acc >>= k
    in flip $ foldl step' pure

  toList : t a -> List a
  toList = foldMap (_:: [])

  concat : t (List a) -> List a
  concat = fold

  concatMap : (a -> List b) -> t a -> List b
  concatMap = foldMap

  length : t a -> Nat
  length = foldr (const suc) zero

  find : (a -> Bool) -> t a -> Maybe a
  find p =
    let step _ x = if p x then left x else right tt
    in either just (const nothing) <<< foldlM step tt

  any : (a -> Bool) -> t a -> Bool
  any p xs = maybe false (const true) (find p xs)

  all : (a -> Bool) -> t a -> Bool
  all p = not <<< any (not <<< p)

  or : t Bool -> Bool
  or = any (_== true)

  and : t Bool -> Bool
  and = all (_== true)

  null : t a -> Bool
  null = foldr (\ _ _ -> false) true

  first : t a -> Maybe a
  first = find (const true)

  last : t a -> Maybe a
  last {a} =
    let step x = maybe (just x) just
    in foldr step nothing

  sum : {{HasAdd a}} -> {{HasNat 0 a}} -> t a -> a
  sum = foldl _+_ 0

  product : {{HasMul a}} -> {{HasNat 1 a}} -> t a -> a
  product = foldl _*_ 1

  module _ {{_ : Eq a}} where

    _elem_ : a -> t a -> Bool
    _elem_ = any <<< _==_

    _notElem_ : a -> t a -> Bool
    x notElem xs = not (x elem xs)

  minimumBy : (a -> a -> Ordering) -> t a -> Maybe a
  minimumBy {a} cmp = foldl min' nothing
    where
      min' : Maybe a -> a -> Maybe a
      min' nothing x = just x
      min' (just x) y = just (if cmp x y == LT then x else y)

  maximumBy : (a -> a -> Ordering) -> t a -> Maybe a
  maximumBy {a} cmp = foldl max' nothing
    where
      max' : Maybe a -> a -> Maybe a
      max' nothing x = just x
      max' (just x) y = just (if cmp x y == GT then x else y)

  module _ {{_ : Ord a}} where

    minimum : t a -> Maybe a
    minimum = minimumBy compare

    maximum : t a -> Maybe a
    maximum = maximumBy compare

  module _ {{_ : Applicative f}} where

    traverse! : (a -> f b) -> t a -> f Unit
    traverse! f = foldr (_*>_ <<< f) (pure tt)

    for! : t a -> (a -> f b) -> f Unit
    for! = flip traverse!

  module _ {{_ : Applicative f}} where

    sequence! : t (f a) -> f Unit
    sequence! = traverse! id

  module _ {{_ : Alternative f}} where

    asum : t (f a) -> f a
    asum = foldr _<|>_ azero

    choice : t (f a) -> f a
    choice ps = foldr _<|>_ azero ps

open Foldable {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Foldable-Maybe : Foldable Maybe
  Foldable-Maybe .foldr f z = maybe z (flip f z)

  Foldable-List : Foldable List
  Foldable-List .foldr f z [] = z
  Foldable-List .foldr f z (x :: xs) = f x (foldr f z xs)
