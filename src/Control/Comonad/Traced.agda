{-# OPTIONS --type-in-type #-}

module Control.Comonad.Traced where

-- Traced M is the dual of Writer W.

Traced : Set -> Set -> Set
Traced M X = M -> X

-- Traced M is a functor.

open import Control.Category
open import Data.Functor

instance
  Functor:Traced : forall {M} -> Endofunctor Sets (Traced M)
  Functor:Traced .map f g = g >>> f

-- Traced M is a comonad whenever M is a monoid.

open import Control.Comonad
open import Data.Monoid

instance
  Comonad:Traced : forall {M} {{_ : Monoid M}} -> Comonad Sets (Traced M)
  Comonad:Traced .duplicate f m m' = f (m <> m')
  Comonad:Traced .extract f = f mempty
