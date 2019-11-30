{-# OPTIONS --type-in-type #-}

module Control.Comonad.Env where

-- The enivornment comonad. This is the dual of the Reader monad.
open import Data.Product
Env : Set → Set → Set
Env E Y = E * Y

private variable E : Set

open import Control.Category
open import Data.Functor
instance Functor:Env : Endofunctor Sets (Env E)
Functor:Env .map f (e , x) = (e , f x)

open import Control.Comonad
instance Comonad:Env : Comonad Sets (Env E) 
Comonad:Env .duplicate (e , x) = (e , (e , x))
Comonad:Env .extract (e , x) = x
