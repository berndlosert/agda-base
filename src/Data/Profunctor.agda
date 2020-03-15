{-# OPTIONS --type-in-type #-}

module Data.Profunctor where

open import Data.Bifunctor public
open import Prelude

private
  variable
    A B C D : Set

record Profunctor (P : Set -> Set -> Set) : Set where
  field
    dimap : (A -> B) -> (C -> D) -> P B C -> P A D

open Profunctor {{...}} public

instance
  Profunctor:Function : Profunctor Function
  Profunctor:Function .dimap f g h = f >>> h >>> g
