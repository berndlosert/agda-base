{-# OPTIONS --type-in-type #-}

module Data.Functor.Product where

-- With this, we can write F * G for product of two endofunctors on Sets.

open import Data.Tuple public

instance
  Mul:Functor : Mul (Set -> Set)
  Mul:Functor = Mul: \ F G X -> F X * G X

-- The product of two endofunctors is a functor.

open import Data.Functor public

instance
  Endofunctor:Product : forall {F G}
    -> {{_ : Endofunctor Sets F}}
    -> {{_ : Endofunctor Sets G}}
    -> Endofunctor Sets (F * G)
  Endofunctor:Product .map f (x , y) = (map f x , map f y)
