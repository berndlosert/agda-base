{-# OPTIONS --type-in-type #-}

module Data.Functor.Coproduct where

open import Prelude

instance
  Add:Functor : Add (Set -> Set)
  Add:Functor ._+_ F G = λ A -> F A + G A

instance
  functorCoproduct : ∀ {F G}
    -> {{_ : Functor F}}
    -> {{_ : Functor G}}
    -> Functor (F + G)
  functorCoproduct .map f (left x) = left (map f x)
  functorCoproduct .map f (right x) = right (map f x)
