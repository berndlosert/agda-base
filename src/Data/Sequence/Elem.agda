module Data.Sequence.Elem where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

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
    a b v : Set
    t : Set -> Set

-------------------------------------------------------------------------------
-- Elem
-------------------------------------------------------------------------------

record Elem (a : Set) : Set where
  constructor asElem
  field getElem : a

open Elem public

instance
  Measured-Elem : Measured (Sum Nat) (Elem a)
  Measured-Elem .measure _ = asSum 1

  Functor-Elem : Functor Elem
  Functor-Elem .map f (asElem x) = asElem (f x)

  Foldable-Elem : Foldable Elem
  Foldable-Elem .foldr step init (asElem x) = step x init

  Traversable-Elem : Traversable Elem
  Traversable-Elem .traverse f (asElem x) = (| asElem (f x) |)
