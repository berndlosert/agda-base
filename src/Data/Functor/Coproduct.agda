{-# OPTIONS --type-in-type #-}

module Data.Functor.Coproduct where

open import Prelude

-- With this, we can write F + G for coproduct of two endofunctors on Sets.
instance
  Add:Functor : Add (Set -> Set)
  Add:Functor = Add: \ F G X -> F X + G X

-- The coproduct of two endofunctors is a functor.
instance
  Functor:Coproduct : forall {F G}
    -> {{_ : Functor F}}
    -> {{_ : Functor G}}
    -> Functor (F + G)
  Functor:Coproduct .map f (left x) = left (map f x)
  Functor:Coproduct .map f (right x) = right (map f x)
