{-# OPTIONS --type-in-type #-}

module Data.Foldable where

open import Control.Applicative
open import Control.Monad
open import Data.Bool
open import Data.Function
open import Data.Eq
open import Data.Monoid
open import Data.Semigroup
open import Prim

private
  variable
    A B S : Set
    F M : Set -> Set

record Fold (S A : Set) : Set where
  field
    foldMap : {{_ : Monoid B}} -> (A -> B) -> S -> B

  fold : {{_ : Monoid A}} -> S -> A
  fold = foldMap id

  foldr : (A -> B -> B) -> B -> S -> B
  foldr f b as = fromEndo (foldMap (toEndo <<< f) as) b

  foldl : (B -> A -> B) -> B -> S -> B
  foldl f b as =
    (fromEndo <<< fromDual) (foldMap (toDual <<< toEndo <<< flip f) as) b

  foldrM : {{_ : Monad M}} -> (A -> B -> M B) -> B -> S -> M B
  foldrM f b as = let g k a b' = f a b' >>= k in
    foldl g return as b

  foldlM : {{_ : Monad M}} -> (B -> A -> M B) -> B -> S -> M B
  foldlM f b as = let g a k b' = f b' a >>= k in
    foldr g return as b

  --find : (A -> Bool) -> S -> Maybe A
  --find p = let ensure' p = (\ _ -> maybeToLeft unit <<< ensure p) in
  --  leftToMaybe <<< foldlM (ensure' p) unit

  --at : Nat -> S -> Maybe A
  --at n = leftToMaybe <<< foldlM f 0
  --  where
  --    f : Nat -> A -> Either A Nat
  --    f k a = if k == n then left a else right (suc k)

  any : (A -> Bool) -> S -> Bool
  any p = fromAny <<< foldMap (toAny <<< p)

  all : (A -> Bool) -> S -> Bool
  all p = fromAll <<< foldMap (toAll <<< p)

  module _ {{_ : Eq A}} where

    elem : A -> S -> Bool
    elem = any <<< _==_

    notElem : A -> S -> Bool
    notElem a s = not (elem a s)

  module _ {{_ : Applicative F}} where

    traverse! : (A -> F B) -> S -> F Unit
    traverse! f = foldr (_*>_ <<< f) (pure unit)

    for! : S -> (A -> F B) -> F Unit
    for! = flip traverse!

open Fold {{...}} public

sequence! : {{_ : Applicative F}} {{_ : Fold S (F A)}} -> S -> F Unit
sequence! = traverse! id

Foldable : (Set -> Set) -> Set
Foldable F = forall {A} -> Fold (F A) A

module _ {{_ : Foldable F}} where

  or : F Bool -> Bool
  or = foldr _||_ false

  and : F Bool -> Bool
  and = foldr _&&_ true
