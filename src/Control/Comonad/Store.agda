{-# OPTIONS --type-in-type #-}

module Control.Comonad.Store where

-- Store S is the dual of State S.
Store : Set -> Set -> Set
Store S X = (S -> X) * S

-- Store S is a functor.
instance
  Functor:Store : forall {S} -> Endofunctor Sets (Store S)
  Functor:Store .map f (Pair: g s) = Pair: (g >>> f) s

-- Store S is a comonad.
open import Control.Comonad

instance
  Comonad:Store : forall {S} -> Comonad Sets (Store S)
  Comonad:Store = record {
      instance:Functor = Functor:Store;
      coextend = \ { p@(Pair: g s) -> (const (Pair: g , s) , s) };
      extract = apply
    }
