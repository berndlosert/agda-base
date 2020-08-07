module Control.Monad.Codensity where

open import Prelude

private variable f m : Set -> Set

Codensity : (Set -> Set) -> Set -> Set
Codensity f a = forall {b} -> (a -> f b) -> f b

instance
  FunctorCodensity : Functor (Codensity f)
  FunctorCodensity .map f x =  λ k -> x (k ∘ f)

  ApplicativeCodensity : Applicative (Codensity f)
  ApplicativeCodensity .pure x = λ k -> k x
  ApplicativeCodensity ._<*>_ f x = λ k -> f (λ g -> x (λ a -> k (g a)))

  MonadCodensity : Monad (Codensity f)
  MonadCodensity ._>>=_ m f = λ k1 -> m (λ k2 -> (f k2) k1)

toCodensity : {{_ : Monad m}} -> m ~> Codensity m
toCodensity x = x >>=_

fromCodensity : {{_ : Monad m}} -> Codensity m ~> m
fromCodensity f = f return
