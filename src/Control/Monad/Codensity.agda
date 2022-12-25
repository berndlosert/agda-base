module Control.Monad.Codensity where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Constrained

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set
    c m : Set -> Set

-------------------------------------------------------------------------------
-- Codensity
-------------------------------------------------------------------------------

-- Constrained version of Codensity. Taken from "The Constrained-Monad Problem".
record Codensity (c m : Set -> Set) (a : Set) : Set where
  constructor asCodensity
  field runCodensity : forall {b} -> {{c b}} -> (a -> m b) -> m b

open Codensity

lowerCodensity : {{c a}} -> {{ConstrainedMonad c m}} -> Codensity c m a -> m a
lowerCodensity x = runCodensity x returnCM

liftCodensity : {{ConstrainedMonad c m}} -> m a -> Codensity c m a
liftCodensity x = asCodensity (bindCM x)

instance
  Functor-Codensity : Functor (Codensity c m)
  Functor-Codensity .map f x = asCodensity \ k -> runCodensity x (k <<< f)

  Applicative-Codensity : Applicative (Codensity c m)
  Applicative-Codensity ._<*>_ f x = asCodensity \ where
    k -> runCodensity f (\ g -> runCodensity x (k <<< g))
  Applicative-Codensity .pure x = asCodensity \ k -> k x

  Monad-Codensity : Monad (Codensity c m)
  Monad-Codensity ._>>=_ m f = asCodensity \ where
    k1 -> runCodensity m (\ k2 -> runCodensity (f k2) k1)