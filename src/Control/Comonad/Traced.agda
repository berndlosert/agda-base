module Control.Comonad.Traced where

open import Control.Comonad
open import Prelude

private variable m : Set

-- Traced m is the dual of Writer w.
Traced : Set -> Set -> Set
Traced m a = m -> a

instance
  Functor-Traced : Functor (Traced m)
  Functor-Traced .map f g = f ∘ g

  Comonad-Traced : {{_ : Monoid m}} -> Comonad (Traced m)
  Comonad-Traced .extend h t m = h (λ m' -> t (m <> m'))
  Comonad-Traced .extract f = f neutral
