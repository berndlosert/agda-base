{-# OPTIONS --type-in-type #-}

module Data.Foldable where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Constraint.Nonempty
open import Data.Monoid.All
open import Data.Monoid.Any
open import Data.Monoid.Dual
open import Data.Monoid.Endo
open import Data.Monoid.Product
open import Data.Monoid.Sum

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Data.Monoid.All public
open Data.Monoid.Any public
open Data.Monoid.Dual public
open Data.Monoid.Endo public
open Data.Monoid.Product public
open Data.Monoid.Sum public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set
    f m t : Set -> Set

-------------------------------------------------------------------------------
-- Monofoldable
-------------------------------------------------------------------------------

record Monofoldable (s a : Set) : Set where
  field foldMap : {{_ : Monoid b}} -> (a -> b) -> s -> b

  fold : {{_ : Monoid a}} -> s -> a
  fold = foldMap id

  foldr : (a -> b -> b) -> b -> s -> b
  foldr f b as = appEndo (foldMap (Endo: <<< f) as) b

  foldl : (b -> a -> b) -> b -> s -> b
  foldl f b as =
    (appEndo <<< getDual) (foldMap (Dual: <<< Endo: <<< flip f) as) b

  foldrM : {{_ : Monad m}} -> (a -> b -> m b) -> b -> s -> m b
  foldrM f b as = let g k a b' = f a b' >>= k in
    foldl g return as b

  foldlM : {{_ : Monad m}} -> (b -> a -> m b) -> b -> s -> m b
  foldlM f b as = let g a k b' = f b' a >>= k in
    foldr g return as b

  toList : s -> List a
  toList = foldMap [_]

  count : s -> Nat
  count = foldr (const Suc) 0

  all : (a -> Bool) -> s -> Bool
  all p = getAll <<< foldMap (All: <<< p)

  any : (a -> Bool) -> s -> Bool
  any p = getAny <<< foldMap (Any: <<< p)

  null : s -> Bool
  null = foldr (\ _ _ -> False) True

  sum : {{ _ : Monoid (Sum a)}} -> s -> a
  sum = getSum <<< foldMap Sum:

  product : {{ _ : Monoid (Product a)}} -> s -> a
  product = getProduct <<< foldMap Product:

  find : (a -> Bool) -> s -> Maybe a
  find p = leftToMaybe <<<
    foldlM (\ _ a ->  if p a then Left a else Right unit) unit

  module _ {{_ : Eq a}} where

    elem : a -> s -> Bool
    elem = any <<< _==_

    notElem : a -> s -> Bool
    notElem a s = not (elem a s)

  module _ {{_ : Applicative f}} where

    traverse! : (a -> f b) -> s -> f Unit
    traverse! f = foldr (_*>_ <<< f) (pure unit)

    for! : s -> (a -> f b) -> f Unit
    for! = flip traverse!

  module _ {{_ : NonemptyConstraint s}} where

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

    minimum : {{_ : Ord a}} (xs : s) {{_ : Nonempty xs}} -> a
    minimum = foldr1 min

    maximum : {{_ : Ord a}} (xs : s) {{_ : Nonempty xs}} -> a
    maximum = foldr1 max

open Monofoldable {{...}} public

-------------------------------------------------------------------------------
-- Foldable
-------------------------------------------------------------------------------

Foldable : (Set -> Set) -> Set
Foldable t = forall {a} -> Monofoldable (t a) a

module _ {{_ : Foldable t}} where

  or : t Bool -> Bool
  or = foldr _||_ False

  and : t Bool -> Bool
  and = foldr _&&_ True

  module _ {{_ : Applicative f}} where

    sequence! : t (f a) -> f Unit
    sequence! = traverse! id

  module _ {{_ : Alternative f}} where

    asum : t (f a) -> f a
    asum = foldr _<|>_ empty

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Monofoldable-Nat-Unit : Monofoldable Nat Unit
  Monofoldable-Nat-Unit .foldMap f Zero = mempty
  Monofoldable-Nat-Unit .foldMap f (Suc n) = f unit <> foldMap f n

  Foldable-Maybe : Foldable Maybe
  Foldable-Maybe .foldMap = maybe mempty

  Foldable-Const : Foldable (Const a)
  Foldable-Const .foldMap _ _ = mempty
