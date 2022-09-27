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
    a : Set
    f m : Set -> Set

-------------------------------------------------------------------------------
-- Codensity
-------------------------------------------------------------------------------

record Codensity (f : Set -> Set) (a : Set) : Set where
  constructor asCodensity
  field runCodensity : forall {b} -> (a -> f b) -> f b

open Codensity

instance
  Functor-Codensity : Functor (Codensity f)
  Functor-Codensity .map f x = asCodensity \ k -> runCodensity x (k <<< f)

  Applicative-Codensity : Applicative (Codensity f)
  Applicative-Codensity ._<*>_ f x = asCodensity \ where
    k -> runCodensity f (\ g -> runCodensity x (k <<< g))
  Applicative-Codensity .pure x = asCodensity \ k -> k x

  Monad-Codensity : Monad (Codensity f)
  Monad-Codensity ._>>=_ m f = asCodensity \ where
    k1 -> runCodensity m (\ k2 -> runCodensity (f k2) k1)

lowerCodensity : {{Applicative f}} -> Codensity f a -> f a
lowerCodensity x = runCodensity x pure
