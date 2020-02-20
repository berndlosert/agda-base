{-# OPTIONS --type-in-type #-}

module Data.Foldable where

-- A free monoid on a type X consists of a monoid F X together with a function
-- lift : X -> F X such that for any monoid M and any function f : X -> M,
-- there is a unique monoid homomorphism foldMap f : F X -> M satisfying
-- lift >>> foldMap f = f. If F X is a free monoid on X for all X, then
-- the construction F is called a free-monoid constructor. A foldable F is a
-- free monoid constructor without lift, without the monoid requirement on F X
-- and without the unique-monoid-homomorphism requirement on foldMap f.

open import Control.Applicative
open import Control.Category
open import Data.Bool
open import Data.Eq
open import Data.Function
open import Data.List.Base
open import Data.List.Monoid
open import Data.Monoid
open import Data.Nat
open import Data.Unit

record Foldable (F : Set -> Set) : Set where
  constructor Foldable:
  field
    foldMap : forall {X M} {{_ : Monoid M}} -> (X -> M) -> F X -> M

  private
    variable
      X Y : Set
      G : Set -> Set

  ------------------------------------------------------------------------------
  -- Derived operations: overview
  ------------------------------------------------------------------------------

  -- Folds
  fold : {{_ : Monoid X}} -> F X -> X
  foldr : (X -> Y -> Y) -> Y -> F X -> Y
  foldl : (Y -> X -> Y) -> Y -> F X -> Y

  -- Predicates
  null : F X -> Bool
  elem : {{_ : Eq X}} -> X -> F X -> Bool

  -- Traversing operations
  traverse- : {{_ : Applicative G}} -> (X -> G Y) -> F X -> G Unit
  for- : {{_ : Applicative G}} -> F X -> (X -> G Y) -> G Unit

  -- List-related folds.
  toList : F X -> List X

  -- Misc.
  size : F X -> Nat


  ------------------------------------------------------------------------------
  -- Derived operations: details
  ------------------------------------------------------------------------------

  fold = foldMap id
  foldr f y x = foldMap {{Monoid:<<< Sets}} f x y
  foldl f y x = foldMap {{Op (Monoid:<<< Sets)}} (flip f) x y

  null = foldMap {{Monoid:&&}} (const true)
  elem x = foldMap {{Monoid:||}} (_== x)

  traverse- f = foldr (f >>> _*>_) (pure tt)
  for- = flip traverse-

  toList =  foldMap [_]

  size = foldMap (const 1)

open Foldable {{...}} public
