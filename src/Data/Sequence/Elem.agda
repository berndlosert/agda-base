module Data.Sequence.Elem where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Tree.Finger.Digit
open import Data.Tree.Finger.Measured
open import Data.Tree.Finger.Node
open import Data.Monoid.Foldable
open import Data.Monoid.Sum
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b v : Type
    t : Type -> Type

-------------------------------------------------------------------------------
-- Elem
-------------------------------------------------------------------------------

record Elem (a : Type) : Type where
  constructor elem
  field getElem : a

open Elem public

instance
  Measured-Elem : Measured (Sum Nat) (Elem a)
  Measured-Elem .measure _ = asSum 1

  Functor-Elem : Functor Elem
  Functor-Elem .map f (elem x) = elem (f x)

  Foldable-Elem : Foldable Elem
  Foldable-Elem .foldMap f (elem x) = f x

  Traversable-Elem : Traversable Elem
  Traversable-Elem .traverse f (elem x) = (| elem (f x) |)
