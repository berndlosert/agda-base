{-# OPTIONS --type-in-type #-}

module Data.Functor.Coproduct where

-- With this, we can write F + G for coproduct of two endofunctors on Sets.

open import Data.Either public

instance
  Add:Functor : Add (Set -> Set)
  Add:Functor = Add: \ F G X -> F X + G X

-- The coproduct of two endofunctors is a functor.

open import Data.Functor public

instance
  Endofunctor:Coproduct : forall {F G}
    -> {{_ : Endofunctor Sets F}}
    -> {{_ : Endofunctor Sets G}}
    -> Endofunctor Sets (F + G)
  Endofunctor:Coproduct .map f (left x) = left (map f x)
  Endofunctor:Coproduct .map f (right x) = right (map f x)
