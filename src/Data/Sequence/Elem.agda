{-# OPTIONS --type-in-type #-}

module Data.Sequence.Elem where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Nat as Nat using ()
open import Data.Tree.Finger.Digit
open import Data.Tree.Finger.Measured
open import Data.Tree.Finger.Node
open import Data.Foldable
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
  constructor Elem:
  field getElem : a

open Elem public

instance
  Measured-Elem : Measured (Sum Nat) (Elem a)
  Measured-Elem .measure _ = Sum: 1

  Functor-Elem : Functor Elem
  Functor-Elem .map f (Elem: x) = Elem: (f x)

  Foldable-Elem : Foldable Elem
  Foldable-Elem .foldr f z (Elem: x) = f x z

  Traversable-Elem : Traversable Elem
  Traversable-Elem .traverse f (Elem: x) = (| Elem: (f x) |)
