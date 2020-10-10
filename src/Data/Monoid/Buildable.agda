{-# OPTIONS --type-in-type #-}

module Data.Monoid.Buildable where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- IsBuildable
-------------------------------------------------------------------------------

record IsBuildable (s a : Set) : Set where
  field
    {{Monoid-s}} : Monoid s
    singleton : a -> s

  cons : a -> s -> s
  cons x xs = singleton x <> xs

  snoc : s -> a -> s
  snoc xs x = xs <> singleton x

  fromList : List a -> s
  fromList [] = mempty
  fromList (a :: as) = cons a (fromList as)

  fromMaybe : Maybe a -> s
  fromMaybe Nothing = mempty
  fromMaybe (Just a) = singleton a

  replicate : Nat -> a -> s
  replicate n a = applyN (cons a) n mempty

-------------------------------------------------------------------------------
-- Buildable
-------------------------------------------------------------------------------

Buildable : (Set -> Set) -> Set
Buildable t = forall {a} -> IsBuildable (t a) a
