module Data.Foldable where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

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
  foldMap {b} {a} f = foldr step mempty
    where
      step : a -> b -> b
      step x acc = f x <> acc

  foldMapBy : (b -> b -> b) -> b -> (a -> b) -> t a -> b
  foldMapBy {b} step init = foldMap {{monoid}}
    where
      monoid : Monoid b
      monoid .mempty = init
      monoid .Semigroup-super ._<>_ = step

  fold : {{Monoid a}} -> t a -> a
  fold = foldMap id

  foldBy : (a -> a -> a) -> a -> t a -> a
  foldBy step init = foldMapBy step init id

  foldl : (b -> a -> b) -> b -> t a -> b
  foldl {b} {a} step init xs = foldr step' id xs init
    where
      step' : a -> (b -> b) -> b -> b
      step' x k acc = k $! step acc x

  foldlM : {{Monad m}} -> (b -> a -> m b) -> b -> t a -> m b
  foldlM {m} {b} {a} step init xs = foldr step' pure xs init
    where
      step' : a -> (b -> m b) -> b -> m b
      step' x k acc = step acc x >>= k

  foldrM : {{Monad m}} -> (a -> b -> m b) -> b -> t a -> m b
  foldrM {m} {a} {b} step init xs = foldl step' pure xs init
    where
      step' : (b -> m b) -> a -> b -> m b
      step' k x acc = step x acc >>= k

  foldr1 : (a -> a -> a) -> t a -> Maybe a
  foldr1 {a} step = foldr step' nothing
    where
      step' : a -> Maybe a -> Maybe a
      step' _ nothing = nothing
      step' x (just y) = just (step x y)

  foldl1 : (a -> a -> a) -> t a -> Maybe a
  foldl1 {a} step = foldl step' nothing
    where
      step' : Maybe a -> a -> Maybe a
      step' nothing _ = nothing
      step' (just x) y = just (step x y)

  toList : t a -> List a
  toList = foldMap (_:: [])

  concat : t (List a) -> List a
  concat = fold

  concatMap : (a -> List b) -> t a -> List b
  concatMap = foldMap

  length : {{FromNat b}} -> t a -> b
  length = fromNat <<< foldr (const suc) 0

  find : (a -> Bool) -> t a -> Maybe a
  find p =
    let step _ x = if p x then left x else right tt
    in either just (const nothing) <<< foldlM step tt

  any : (a -> Bool) -> t a -> Bool
  any p xs = maybe false (const true) (find p xs)

  all : (a -> Bool) -> t a -> Bool
  all p = not <<< (any (not <<< p))

  or : t Bool -> Bool
  or = any id

  and : t Bool -> Bool
  and = all id

  null : t a -> Bool
  null = foldr (\ _ _ -> false) true

  defaulting : b -> (t a -> b) -> t a -> b
  defaulting d f xs = if null xs then d else f xs

  first : t a -> Maybe a
  first = find (const true)

  last : t a -> Maybe a
  last {a} =
    let step x = maybe (just x) just
    in foldr step nothing

  sum : {{Num a}} -> t a -> a
  sum = foldl _+_ 0

  product : {{Num a}} -> t a -> a
  product = foldl _*_ 1

  module _ {{_ : Eq a}} where

    _elem_ : a -> t a -> Bool
    _elem_ = any <<< _==_

    _notElem_ : a -> t a -> Bool
    x notElem xs = not (x elem xs)

  minimumBy : (a -> a -> Ordering) -> t a -> Maybe a
  minimumBy {a} cmp = foldl step nothing
    where
      step : Maybe a -> a -> Maybe a
      step nothing x = just x
      step (just acc) x = just (if cmp acc x == LT then acc else x)

  maximumBy : (a -> a -> Ordering) -> t a -> Maybe a
  maximumBy {a} cmp = foldl step nothing
    where
      step : Maybe a -> a -> Maybe a
      step nothing x = just x
      step (just acc) x = just (if cmp acc x == GT then acc else x)

  module _ {{_ : Ord a}} where

    minimum : t a -> Maybe a
    minimum = minimumBy compare

    maximum : t a -> Maybe a
    maximum = maximumBy compare

  module _ {{_ : Applicative f}} where

    traverse* : (a -> f b) -> t a -> f Unit
    traverse* f = foldr (_*>_ <<< f) (pure tt)

    for* : t a -> (a -> f b) -> f Unit
    for* = flip traverse*

  module _ {{_ : Applicative f}} where

    sequence* : t (f a) -> f Unit
    sequence* = traverse* id

  module _ {{_ : Alternative f}} where

    asum : t (f a) -> f a
    asum = foldr _<|>_ azero

open Foldable {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Foldable-Maybe : Foldable Maybe
  Foldable-Maybe .foldr step init = maybe init (flip step init)

  Foldable-List : Foldable List
  Foldable-List .foldr step init [] = init
  Foldable-List .foldr step init (x :: xs) = step x (foldr step init xs)
