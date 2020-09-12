{-# OPTIONS --type-in-type #-}

module Data.Functor.Yoneda where

open import Prelude

private
  variable
    a b : Set
    f : Set -> Set

Yoneda : (Set -> Set) -> Set -> Set
Yoneda f a = forall {b} -> (a -> b) -> f b

instance
  Functor-Yoneda : Functor (Yoneda f)
  Functor-Yoneda .map f t g = t (g <<< f)

lift : {{_ : Functor f}} -> f a -> Yoneda f a
lift y f = map f y

lower : Yoneda f a -> f a
lower t = t id
