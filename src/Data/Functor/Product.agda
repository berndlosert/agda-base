{-# OPTIONS --type-in-type #-}

module Data.Functor.Product where

open import Prelude

-- With this, we can write F * G for product of two endofunctors on Sets.
instance
  Mul:Functor : Mul (Set -> Set)
  Mul:Functor ._*_ F G = \ A -> F A * G A

-- The product of two endofunctors is a functor.
instance
  functorProduct : forall {F G}
    -> {{_ : Functor F}}
    -> {{_ : Functor G}}
    -> Functor (F * G)
  functorProduct .map f (x , y) = (map f x , map f y)
