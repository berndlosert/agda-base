{-# OPTIONS --type-in-type #-}

module Control.Monad.Codensity where

-- Codensity F is a monad for any F in the same sense that X -> X is a monoid
-- for any X. And just like any monoid M is a submonoid of X -> X, any monad M
-- is a "submonad" of Codensity M.

open import Control.Category
open import Control.Monad
open import Data.Functor

Codensity : (Set -> Set) -> Set -> Set
Codensity F X = forall {Y} -> (X -> F Y) -> F Y

instance
  Functor:Codensity : forall {F} -> Endofunctor Sets (Codensity F)
  Functor:Codensity .map f alpha g = alpha (f >>> g)

  Monad:Codensity : forall {F} -> Monad Sets (Codensity F)
  Monad:Codensity .join k g = k (\ k' -> k' g)
  Monad:Codensity .return x f = f x
