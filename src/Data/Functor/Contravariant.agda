{-# OPTIONS --type-in-type #-}

module Data.Functor.Contravariant where

open import Prelude

private
  variable
    A B : Set
    F : Set -> Set

record Contravariant (F : Set -> Set) : Set where
  field
    contramap : (A -> B) -> F B -> F A

open Contravariant {{...}} public

phantom : {{_ : Functor F}} {{_ : Contravariant F}} -> F A -> F B
phantom x = contramap (const tt) $ map (const tt) x
