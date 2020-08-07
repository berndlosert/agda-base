module Control.Comonad.Traced where

open import Control.Comonad
open import Prelude

private variable m : Set

-- Traced m is the dual of Writer w.
Traced : Set -> Set -> Set
Traced m a = m -> a

instance
  FunctorTraced : Functor (Traced m)
  FunctorTraced .map f g = f ∘ g

  ComonadTraced : {{_ : Monoid m}} -> Comonad (Traced m)
  ComonadTraced .extend h t m = h $ λ m' -> t (m <> m')
  ComonadTraced .extract f = f neutral
