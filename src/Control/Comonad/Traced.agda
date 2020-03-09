{-# OPTIONS --type-in-type #-}

module Control.Comonad.Traced where

open import Prelude

-- Traced M is the dual of Writer W.
Traced : Set -> Set -> Set
Traced M X = M -> X

-- Traced M is a functor.
instance
  Functor:Traced : forall {M} -> Functor Sets Sets (Traced M)
  Functor:Traced .map f g = g >>> f

-- Traced M is a comonad whenever M is a monoid.
open import Control.Comonad

instance
  Comonad:Traced : forall {M} {{_ : Monoid M}} -> Comonad Sets (Traced M)
  Comonad:Traced .coextend h t m = h $ \ m' -> t (m <> m')
  Comonad:Traced .extract f = f mempty
