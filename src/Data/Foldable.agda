{-# OPTIONS --type-in-type #-}

module Data.Foldable where

-- A free monoid on a type X consists of a monoid F X together with a function
-- singleton : X -> F X such that for any monoid M and any function f : X -> M,
-- there is a unique monoid homomorphism foldMap f : F X -> M satisfying
-- singleton >>> foldMap f = f. If F X is a free monoid on X for all X, then
-- the construction F is called a free-monoid constructor. A foldable F is
-- a free monoid constructor without the monoid requirement on F X and the
-- unique-monoid-homomorphism requirement on foldMap f.

open import Control.Applicative
open import Control.Category
open import Data.Bool
open import Data.Function
open import Data.List.Base
open import Data.Monoid
open import Data.Nat

record Foldable (F : Set -> Set) : Set where
  constructor Foldable:
  field
    singleton : {X : Set} -> X -> F X
    foldMap : {M : Set} {{_ : Monoid M}} {X : Set}
      -> (X -> M) -> F X -> M

  private
    variable
      G : Set -> Set
      X Y : Set

  fold : {{_ : Monoid X}} -> F X -> X
  fold = foldMap id

  foldr : (X -> Y -> Y) -> Y -> F X -> Y
  foldr f y x = foldMap {{Monoid:<<<}} f x y

  foldl : (Y -> X -> Y) -> Y -> F X -> Y
  foldl f = foldr (flip f)

  toList : F X -> List X
  toList x = foldMap [_] x

  null : F X -> Bool
  null = foldMap {{Monoid:&&}} (const true)

  size : F X -> Nat
  size = foldMap $ const $ suc zero

  elem : {{_ : Eq X}} -> X -> F X -> Bool
  elem x = foldMap {{Monoid:||}} (_== x)

  -- Constraint indicating that an F X is not empty.
  Nonempty : F X -> Set
  Nonempty xs = Constraint (not (null xs))

  traverse- : {{_ : Applicative G}} -> (X -> G Y) -> F X -> G Unit
  traverse- f = foldr (f >>> _*>_) (pure tt)

  for- : {{_ : Applicative G}} -> F X -> (X -> G Y) -> G Unit
  for- = flip traverse-

open Foldable {{...}} public
