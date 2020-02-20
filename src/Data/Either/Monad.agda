{-# OPTIONS --type-in-type #-}

module Data.Either.Monad where

open import Control.Monad public
open import Data.Either.Base
open import Data.Either.Functor

instance
  Monad:Either : forall {X} -> Monad Sets (Either X)
  Monad:Either .return y = right y
  Monad:Either .extend f (right y) = f y
  Monad:Either .extend f (left x) = left x
