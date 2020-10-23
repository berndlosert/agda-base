{-# OPTIONS --type-in-type #-}

module Data.FingerTree.Digit where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable
open import Data.FingerTree.Measured
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a v : Set

-------------------------------------------------------------------------------
-- Digit
-------------------------------------------------------------------------------

data Digit (a : Set) : Set where
  One : a -> Digit a
  Two : a -> a -> Digit a
  Three : a -> a -> a -> Digit a
  Four : a -> a -> a -> a -> Digit a

instance
  Foldable-Digit : Foldable Digit
  Foldable-Digit .foldMap f digit with digit
  ... | One a = f a
  ... | Two a b = f a <> f b
  ... | Three a b c = f a <> f b <> f c
  ... | Four a b c d = f a <> f b <> f c <> f d

  Functor-Digit : Functor Digit
  Functor-Digit .map f digit with digit
  ... | One a = One (f a)
  ... | Two a b = Two (f a) (f b)
  ... | Three a b c = Three (f a) (f b) (f c)
  ... | Four a b c d = Four (f a) (f b) (f c) (f d)

  Traversable-Digit : Traversable Digit
  Traversable-Digit .traverse f digit with digit
  ... | One a = (| One (f a) |)
  ... | Two a b = (| Two (f a) (f b) |)
  ... | Three a b c = (| Three (f a) (f b) (f c) |)
  ... | Four a b c d = (| Four (f a) (f b) (f c) (f d) |)

  Measured-Digit : {{_ : Measured v a}} -> Measured v (Digit a)
  Measured-Digit .measure = foldMap measure
