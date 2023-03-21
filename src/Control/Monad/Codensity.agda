module Control.Monad.Codensity where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set
    m : Set -> Set

-------------------------------------------------------------------------------
-- Codensity
-------------------------------------------------------------------------------

record Codensity (m : Set -> Set) (a : Set) : Set where
  constructor asCodensity
  field runCodensity : (a -> m b) -> m b

open Codensity

lowerCodensity : {{Monad m}} -> Codensity m a -> m a
lowerCodensity x = runCodensity x pure

liftCodensity : {{Monad m}} -> m a -> Codensity m a
liftCodensity x = asCodensity (x >>=_)

instance
  Functor-Codensity : Functor (Codensity m)
  Functor-Codensity .map f x = asCodensity \ k -> runCodensity x (k <<< f)

  Applicative-Codensity : Applicative (Codensity m)
  Applicative-Codensity ._<*>_ f x = asCodensity \ where
    k -> runCodensity f (\ g -> runCodensity x (k <<< g))
  Applicative-Codensity .pure x = asCodensity \ k -> k x

  Monad-Codensity : Monad (Codensity m)
  Monad-Codensity ._>>=_ m f = asCodensity \ where
    k1 -> runCodensity m (\ k2 -> runCodensity (f k2) k1)