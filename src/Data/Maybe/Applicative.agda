{-# OPTIONS --type-in-type #-}

module Data.Maybe.Applicative where

open import Control.Applicative public
open import Control.Monad
open import Data.Maybe.Base
open import Data.Maybe.Functor
open import Data.Maybe.Monad

instance
  Applicative:Maybe : Applicative Maybe
  Applicative:Maybe = Applicative: ap return
