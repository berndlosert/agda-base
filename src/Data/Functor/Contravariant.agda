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

  phantom : {{_ : Functor F}} -> F A -> F B
  phantom x = contramap (const unit) $ map (const unit) x

open Contravariant {{...}} public


