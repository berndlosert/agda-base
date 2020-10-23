{-# OPTIONS --type-in-type #-}

module Data.Buildable where

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

  infixr 5 _<|_
  _<|_ : a -> s -> s
  x <| xs = singleton x <> xs

  infixl 5 _|>_
  _|>_ : s -> a -> s
  xs |> x = xs <> singleton x

  fromList : List a -> s
  fromList [] = mempty
  fromList (a :: as) = a <| (fromList as)

  fromMaybe : Maybe a -> s
  fromMaybe Nothing = mempty
  fromMaybe (Just a) = singleton a

  replicate : Nat -> a -> s
  replicate n a = applyN (a <|_) n mempty

open Monobuildable {{...}} public

-------------------------------------------------------------------------------
-- Buildable
-------------------------------------------------------------------------------

Buildable : (Set -> Set) -> Set
Buildable t = forall {a} -> Monobuildable (t a) a

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Buildable-List : Buildable List
  Buildable-List .singleton = _:: []

  Monobuildable-String-Char : Monobuildable String Char
  Monobuildable-String-Char .singleton = pack <<< singleton
