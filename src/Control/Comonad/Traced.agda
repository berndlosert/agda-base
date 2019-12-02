{-# OPTIONS --type-in-type #-}

module Control.Comonad.Traced where

open import Control.Category
open import Control.Comonad
open import Data.Functor
open import Data.Monoid

-- Traced M is the dual of Writer W.
Traced : Set -> Set -> Set
Traced M X = M -> X

private variable M : Set

instance
  Functor:Traced : Endofunctor Sets (Traced M)
  Functor:Traced .map f g = g >>> f

  Comonad:Traced : {{_ : Monoid M}} -> Comonad Sets (Traced M)
  Comonad:Traced .duplicate f m m' = f (m <> m')
  Comonad:Traced .extract f = f mempty
