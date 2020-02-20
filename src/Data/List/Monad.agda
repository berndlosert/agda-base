{-# OPTIONS --type-in-type #-}

module Data.List.Monad where

open import Control.Category
open import Control.Monad public
open import Data.List.Base
open import Data.List.Functor

instance
  Monad:List : Monad Sets List
  Monad:List .return = [_]
  Monad:List .extend k [] = []
  Monad:List .extend k (x :: xs) = k x ++ extend k xs
