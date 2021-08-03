{-# OPTIONS --type-in-type #-}

module Control.Monad.Codensity where

open import Prelude

private
  variable
    a : Type
    f m : Type -> Type

Codensity : (Type -> Type) -> Type -> Type
Codensity f a = forall {b} -> (a -> f b) -> f b

instance
  Functor-Codensity : Functor (Codensity f)
  Functor-Codensity .map f x =  \ k -> x (k <<< f)

  Applicative-Codensity : Applicative (Codensity f)
  Applicative-Codensity .pure x = \ k -> k x
  Applicative-Codensity ._<*>_ f x = \ k -> f (\ g -> x (\ a -> k (g a)))

  Monad-Codensity : Monad (Codensity f)
  Monad-Codensity ._>>=_ m f = \ k1 -> m (\ k2 -> (f k2) k1)

toCodensity : {{Monad m}} -> m a -> Codensity m a
toCodensity x = x >>=_

fromCodensity : {{Monad m}} -> Codensity m a -> m a
fromCodensity f = f return
