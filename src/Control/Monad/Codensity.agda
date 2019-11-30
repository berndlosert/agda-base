{-# OPTIONS --type-in-type #-}

module Control.Monad.Codensity where

open import Control.Category
open import Control.Monad
open import Data.Functor

Codensity : (F : Set → Set) {{_ : Endofunctor Sets F}} → Set → Set
Codensity F X = {Y : Set} → (X → F Y) → F Y

instance
  Functor:Codensity : {F : Set → Set} {{_ : Endofunctor Sets F}}
    → Endofunctor Sets (Codensity F)
  Functor:Codensity .map f alpha g = alpha (f >>> g)

  Monad:Codensity : {F : Set → Set} {{_ : Endofunctor Sets F}}
    → Monad Sets (Codensity F)
  Monad:Codensity .join k g = k (\ k' → k' g)
  Monad:Codensity .return x f = f x
