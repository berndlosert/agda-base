{-# OPTIONS --type-in-type #-}

module Data.Maybe.Functor where

open import Data.Functor public
open import Data.Maybe.Base

instance
  Functor:Maybe : Endofunctor Sets Maybe
  Functor:Maybe .map f nothing = nothing
  Functor:Maybe .map f (just x) = just (f x)
