{-# OPTIONS --type-in-type #-}

module Control.Comonad.Traced where

open import Control.Comonad
open import Prelude

private variable m : Set

-- Traced m is the dual of Writer w.
Traced : Set -> Set -> Set
Traced m a = m -> a

instance
  functorTraced : Functor (Traced m)
  functorTraced .map f g = f ∘ g

  comonadTraced : {{_ : Monoid m}} -> Comonad (Traced m)
  comonadTraced .extend h t m = h $ λ m' -> t (m <> m')
  comonadTraced .extract f = f neutral
