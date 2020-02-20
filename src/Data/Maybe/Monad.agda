{-# OPTIONS --type-in-type #-}

module Data.Maybe.Monad where

open import Control.Category
open import Control.Monad public
open import Data.Maybe.Base
open import Data.Maybe.Functor

instance
  Monad:Maybe : Monad Sets Maybe
  Monad:Maybe .return = just
  Monad:Maybe .extend k nothing = nothing
  Monad:Maybe .extend k (just x) = k x
