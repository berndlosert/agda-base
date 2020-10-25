{-# OPTIONS --type-in-type #-}

module Data.Buildable where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set
    f : Set -> Set

-------------------------------------------------------------------------------
-- Buildable
-------------------------------------------------------------------------------

record Buildable (s a : Set) : Set where
  field
    nil : s
    singleton : a -> s
    cons : a -> s -> s
    snoc : s -> a -> s
    append : s -> s -> s

  consAll : {{_ : Foldable f}} -> f a -> s -> s
  consAll = flip (foldr cons)

  snocAll : {{_ : Foldable f}} -> s -> f a -> s
  snocAll = foldl snoc

  fromList : List a -> s
  fromList xs = consAll xs nil

  fromMaybe : Maybe a -> s
  fromMaybe m = consAll m nil

  replicate : Nat -> a -> s
  replicate n a = applyN (cons a) n nil

open Buildable {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Buildable-List : Buildable (List a) a
  Buildable-List .nil = []
  Buildable-List .singleton = _:: []
  Buildable-List .cons = _::_
  Buildable-List .snoc xs x = xs <> [ x ]
  Buildable-List .append = _<>_
