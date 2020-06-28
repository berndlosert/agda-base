{-# OPTIONS --type-in-type #-}

module Control.Monad.Codensity where

-- Codensity F is a monad for any F in the same sense that X -> X is a monoid
-- for any X.

open import Control.Category
open import Control.Monad
open import Data.Functor

Codensity : (Set -> Set) -> Set -> Set
Codensity F X = forall {Y} -> (X -> F Y) -> F Y

instance
  monadCodensity : forall {F} -> Monad (Codensity F)
  monadCodensity .return x = λ k -> k x
  monadCodensity .extend f m = λ k1 -> m (λ k2 -> (f k2) k1)

-- And just like any monoid M is a submonoid of X -> X, any monad M is a
-- "submonad" of Codensity M. The embedding of X in X -> X assigns to each x :
-- X the function x <>_ : X -> X; in the monad case, the embedding assings each
-- x : M X to x >>=_ : Codensity M X.

rep : forall {M} {{_ : Monad M}} -> M ~> Codensity M
rep x = x >>=_

-- The left-inverse (retract) of rep for the monoid case assigns f : X -> X to
-- f empty. The monad version assigns each f : Codensity M X the value
-- f return.

abs : forall {M} {{_ : Monad M}} -> Codensity M ~> M
abs f = f return
