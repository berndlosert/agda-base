{-# OPTIONS --type-in-type #-}

module Data.Either.Functor where

open import Data.Functor public
open import Data.Either.Base public

instance
  Functor:Either : forall {X} -> Endofunctor Sets (Either X)
  Functor:Either .map f (left x) = left x
  Functor:Either .map f (right y) = right (f y)
