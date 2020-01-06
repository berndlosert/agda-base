{-# OPTIONS --type-in-type #-}

module Control.Comonad.Store where

-- Store S is the dual of State S.

open import Data.Pair

Store : Set -> Set -> Set
Store S X = (S -> X) * S

-- Store S is a functor.

open import Control.Category
open import Data.Functor

instance
  Functor:Store : forall {S} -> Endofunctor Sets (Store S)
  Functor:Store .map f (g , s) = (g >>> f , s)

-- Store S is a comonad.

open import Control.Comonad
open import Data.Function

instance
  Comonad:Store : forall {S} -> Comonad Sets (Store S)
  Comonad:Store = record {
      instance:Functor = Functor:Store;
      duplicate = \ { (g , s) -> (const (g , s) , s) };
      extract = apply
    }
