{-# OPTIONS --type-in-type #-}

module Data.Functor.Contravariant where

open import Prelude

Contravariant = FunctorOf (Op Sets) Sets

contramap : forall {F} {{_ : Contravariant F}}
  -> forall {X Y} -> (X -> Y) -> F Y -> F X
contramap = map

phantom : forall {F} {{_ : Functor F}} {{_ : Contravariant F}}
  -> forall {X Y} -> F X -> F Y
phantom x = contramap (const tt) $ map (const tt) x
