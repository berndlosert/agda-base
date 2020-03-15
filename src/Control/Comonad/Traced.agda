{-# OPTIONS --type-in-type #-}

module Control.Comonad.Traced where

open import Control.Comonad
open import Prelude

private
  variable
    M : Set

-- Traced M is the dual of Writer W.
Traced : Set -> Set -> Set
Traced M X = M -> X

instance
  Functor:Traced : Functor (Traced M)
  Functor:Traced .map f g = g >>> f

  Comonad:Traced : {{_ : Monoid M}} -> Comonad (Traced M)
  Comonad:Traced .extend h t m = h $ \ m' -> t (m <> m')
  Comonad:Traced .extract f = f mempty
