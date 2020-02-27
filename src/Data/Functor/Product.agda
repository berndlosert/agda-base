{-# OPTIONS --type-in-type #-}

module Data.Functor.Product where

open import Prelude

-- With this, we can write F * G for product of two endofunctors on Sets.
instance
  Mul:Functor : Mul (Set -> Set)
  Mul:Functor = Mul: \ F G X -> F X * G X

-- The product of two endofunctors is a functor.
instance
  Endofunctor:Product : forall {F G}
    -> {{_ : Endofunctor Sets F}}
    -> {{_ : Endofunctor Sets G}}
    -> Endofunctor Sets (F * G)
  Endofunctor:Product .map f (Pair: x y) = Pair: (map f x) (map f y)
