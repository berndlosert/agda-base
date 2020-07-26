module Control.Monad.Codensity where

open import Prelude

private variable f m : Set -> Set

Codensity : (Set -> Set) -> Set -> Set
Codensity f a = forall {b} -> (a -> f b) -> f b

instance
  functorCodensity : Functor (Codensity f)
  functorCodensity .map f x =  λ k -> x (k ∘ f)

  applicativeCodensity : Applicative (Codensity f)
  applicativeCodensity .pure x = λ k -> k x
  applicativeCodensity ._<*>_ f x = λ k -> f (λ g -> x (λ a -> k (g a)))

  monadCodensity : Monad (Codensity f)
  monadCodensity ._>>=_ m f = λ k1 -> m (λ k2 -> (f k2) k1)

toCodensity : {{_ : Monad m}} -> m ~> Codensity m
toCodensity x = x >>=_

fromCodensity : {{_ : Monad m}} -> Codensity m ~> m
fromCodensity f = f return
