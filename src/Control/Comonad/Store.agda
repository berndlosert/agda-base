{-# OPTIONS --type-in-type #-}

module Control.Comonad.Store where

open import Control.Category
open import Control.Comonad
open import Data.Function
open import Data.Functor
open import Data.Product

-- Store S is the dual of State S.
Store : Set → Set → Set
Store S X = (S → X) * S

private variable S : Set

instance
  Functor:Store : Endofunctor Sets (Store S)
  Functor:Store .map f (g , s) = (g >>> f , s) 

  Comonad:Store : Comonad Sets (Store S)
  Comonad:Store .duplicate (g , s) = (const (g , s) , s)
  Comonad:Store .extract = apply 
