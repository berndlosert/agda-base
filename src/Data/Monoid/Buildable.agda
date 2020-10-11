{-# OPTIONS --type-in-type #-}

module Data.Monoid.Buildable where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Monobuildable
-------------------------------------------------------------------------------

record Monobuildable (s a : Set) : Set where
  field
    {{Monoid-s}} : Monoid s
    singleton : a -> s

  nil : s
  nil = mempty

  infixr 5 _++_
  _++_ : s -> s -> s
  _++_ = _<>_

  cons : a -> s -> s
  cons x xs = singleton x ++ xs

  snoc : s -> a -> s
  snoc xs x = xs ++ singleton x

  fromList : List a -> s
  fromList [] = nil
  fromList (a :: as) = cons a (fromList as)

  fromMaybe : Maybe a -> s
  fromMaybe Nothing = nil
  fromMaybe (Just a) = singleton a

  replicate : Nat -> a -> s
  replicate n a = applyN (cons a) n nil

open Monobuildable {{...}} public

-------------------------------------------------------------------------------
-- Buildable
-------------------------------------------------------------------------------

Buildable : (Set -> Set) -> Set
Buildable t = forall {a} -> Monobuildable (t a) a
