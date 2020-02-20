{-# OPTIONS --type-in-type #-}

module Data.Either.Applicative where

open import Control.Applicative public
open import Control.Monad public
open import Data.Either.Base
open import Data.Either.Functor
open import Data.Either.Monad

instance
  Applicative:Either : forall {X} -> Applicative (Either X)
  Applicative:Either = Applicative: ap return
