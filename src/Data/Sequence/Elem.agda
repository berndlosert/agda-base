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

traverseNE : {{_ : Applicative t}}
  -> (a -> t b) -> Node v (Elem a) -> t (Node v (Elem b))
traverseNE g node = (| getCompose (traverse g (Compose: node)) |)

traverseDE : {{_ : Applicative t}}
  -> (a -> t b) -> Digit (Elem a) -> t (Digit (Elem b))
traverseDE g digit = (| getCompose (traverse g (Compose: digit)) |)
