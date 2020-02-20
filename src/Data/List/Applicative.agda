{-# OPTIONS --type-in-type #-}

module Data.List.Applicative where

open import Control.Applicative public
open import Data.List.Base
open import Data.List.Functor
open import Data.List.Monad

instance
  Applicative:List : Applicative List
  Applicative:List = Applicative: ap return
