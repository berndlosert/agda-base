module Control.Monad.Codensity where

open import Prelude

private variable f m : Set -> Set

Codensity : (Set -> Set) -> Set -> Set
Codensity f a = forall {b} -> (a -> f b) -> f b

instance
  Functor-Codensity : Functor (Codensity f)
  Functor-Codensity .map f x =  λ k -> x (k ∘ f)

  Applicative-Codensity : Applicative (Codensity f)
  Applicative-Codensity .pure x = λ k -> k x
  Applicative-Codensity ._<*>_ f x = λ k -> f (λ g -> x (λ a -> k (g a)))

  Monad-Codensity : Monad (Codensity f)
  Monad-Codensity ._>>=_ m f = λ k1 -> m (λ k2 -> (f k2) k1)

toCodensity : {{_ : Monad m}} -> m ~> Codensity m
toCodensity x = x >>=_

fromCodensity : {{_ : Monad m}} -> Codensity m ~> m
fromCodensity f = f return
