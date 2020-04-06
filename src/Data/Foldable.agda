{-# OPTIONS --type-in-type #-}

module Data.Foldable where

open import Control.Applicative using (Applicative; _*>_; pure)
open import Control.Monad using (Monad; _>>=_; return)
open import Data.Function using (id; _<<<_; flip; const)
open import Data.Boolean using (Boolean; tt; ff; _&&_; _||_)
open import Data.Bool using (Bool; false; true; if_then_else_; not)
open import Data.Either using (Either; left; right; untag)
open import Data.Eq using (Eq; _==_)
open import Data.Maybe using (Maybe; maybeToLeft; ensure; leftToMaybe; isJust)
open import Data.Monoid using (Monoid)
open import Data.Nat using (Nat; suc)
open import Data.Semigroup using (fromEndo; toEndo)
open import Data.Semigroup using (fromDual; toDual)
open import Data.Unit using (Unit; unit)

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

  null : S -> Bool
  null = untag <<< foldlM (\ _ _ -> left false) true

  length : S -> Nat
  length = foldr (const suc) 0

  find : (A -> Bool) -> S -> Maybe A
  find p = let ensure' p = (\ _ -> maybeToLeft unit <<< ensure p) in
    leftToMaybe <<< foldlM (ensure' p) unit

  at : Nat -> S -> Maybe A
  at n = leftToMaybe <<< foldlM f 0
    where
      f : Nat -> A -> Either A Nat
      f k a = if k == n then left a else right (suc k)

  any : (A -> Bool) -> S -> Bool
  any p = isJust <<< find p

  all : (A -> Bool) -> S -> Bool
  all p = not <<< any (not <<< p)

  module _ {{_ : Eq A}} where

    elem : A -> S -> Bool
    elem = any <<< _==_

    notElem : A -> S -> Bool
    notElem x = not <<< elem x

  module _ {{_ : Applicative F}} where

    traverse! : (A -> F B) -> S -> F Unit
    traverse! f = foldr (_*>_ <<< f) (pure unit)

    for! : S -> (A -> F B) -> F Unit
    for! = flip traverse!

  module _ {{_ : Boolean A}} where

    or : S -> A
    or = foldr _||_ ff

    and : S -> A
    and = foldr _&&_ tt

open Fold {{...}} public

sequence! : {{_ : Applicative F}} {{_ : Fold S (F A)}} -> S -> F Unit
sequence! = traverse! id

Foldable : (Set -> Set) -> Set
Foldable T = forall {A} -> Fold (T A) A
