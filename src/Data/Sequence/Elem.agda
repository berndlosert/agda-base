{-# OPTIONS --type-in-type #-}

module Data.Sequence.Elem where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.FingerTree.Digit
open import Data.FingerTree.Measured
open import Data.FingerTree.Node
open import Data.Foldable
open import Data.Functor.Compose
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b v : Set
    t : Set -> Set

-------------------------------------------------------------------------------
-- Elem
-------------------------------------------------------------------------------

record Elem (a : Set) : Set where
  constructor Elem:
  field getElem : a

open Elem public

instance
  Measured-Elem : Measured (Sum Nat) (Elem a)
  Measured-Elem .measure _ = Sum: 1

  Functor-Elem : Functor Elem
  Functor-Elem .map f (Elem: x) = Elem: (f x)

  Foldable-Elem : Foldable Elem
  Foldable-Elem .foldMap f (Elem: x) = f x

  Traversable-Elem : Traversable Elem
  Traversable-Elem .traverse f (Elem: x) = (| Elem: (f x) |)