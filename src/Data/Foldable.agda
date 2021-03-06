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
-- Foldable
-------------------------------------------------------------------------------

record Foldable (t : Type -> Type) : Type where
  field foldr : (a -> b -> b) -> b -> t a -> b

  foldMap : {{_ : Monoid b}} -> (a -> b) -> t a -> b
  foldMap f = foldr (_<>_ <<< f) neutral

  fold : {{_ : Monoid a}} -> t a -> a
  fold = foldMap id

  foldl : (b -> a -> b) -> b -> t a -> b
  foldl f z xs = foldr (_>>>_ <<< flip f) id xs z

  foldrM : {{_ : Monad m}} -> (a -> b -> m b) -> b -> t a -> m b
  foldrM f z xs = let g k y z' = f y z' >>= k in
    foldl g return xs z

  foldlM : {{_ : Monad m}} -> (b -> a -> m b) -> b -> t a -> m b
  foldlM f z xs = let g y k z' = f z' y >>= k in
    foldr g return xs z

  toList : t a -> List a
  toList = foldMap (_:: [])

  concat : t (List a) -> List a
  concat = fold

  concatMap : (a -> List b) -> t a -> List b
  concatMap = foldMap

  length : t a -> Nat
  length = foldr (const Suc) 0

  find : (a -> Bool) -> t a -> Maybe a
  find p = either Just (const Nothing) <<<
    foldlM (\ _ x ->  if p x then Left x else Right unit) unit

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

  module _ {{_ : Validation Nonempty (t a)}} where

    foldMap1 : {{_ : Semigroup b}}
      -> (a -> b) -> (xs : t a) {{_ : Validate {Nonempty} xs}} -> b
    foldMap1 f s = fromJust (foldMap (Just <<< f) s) {{trustMe}}

    fold1 : {{_ : Semigroup a}} (xs : t a) {{_ : Validate {Nonempty} xs}} -> a
    fold1 s = fromJust (foldMap Just s) {{trustMe}}

    foldr1 : (a -> a -> a) -> (xs : t a) {{_ : Validate {Nonempty} xs}} -> a
    foldr1 f s = fromJust (foldr g Nothing s) {{trustMe}}
      where
        g : a -> Maybe a -> Maybe a
        g x Nothing = Just x
        g x (Just y) = Just (f x y)

    foldl1 : (a -> a -> a) -> (xs : t a) {{_ : Validate {Nonempty} xs}} -> a
    foldl1 f s = fromJust (foldl g Nothing s) {{trustMe}}
      where
        g : Maybe a -> a -> Maybe a
        g Nothing x = Just x
        g (Just x) y = Just (f x y)

    module _ {{_ : Ord a}} where

      minimum : (xs : t a) {{_ : Validate {Nonempty} xs}} -> a
      minimum = foldr1 min

      maximum : (xs : t a) {{_ : Validate {Nonempty} xs}} -> a
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
