{-# OPTIONS --type-in-type #-}

module Data.Maybe.Alternative where

open import Control.Alternative public
open import Data.Maybe.Base
open import Data.Maybe.Applicative

instance
  Alternative:Maybe : Alternative Maybe
  Alternative:Maybe ._<|>_ nothing nothing = nothing
  Alternative:Maybe ._<|>_ (just x) nothing = just x
  Alternative:Maybe ._<|>_ nothing (just x) = just x
  Alternative:Maybe ._<|>_ (just x) (just y) = just x
  Alternative:Maybe .empty = nothing
