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
  functorTraced : Functor (Traced M)
  functorTraced .map f g = f <<< g

  comonadTraced : {{_ : Monoid M}} -> Comonad (Traced M)
  comonadTraced .extend h t m = h $ \ m' -> t (m <> m')
  comonadTraced .extract f = f empty
