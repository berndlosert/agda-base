{-# OPTIONS --type-in-type #-}

module Data.List.Functor where

open import Data.List.Base
open import Data.Functor public

instance
  Functor:List : Endofunctor Sets List
  Functor:List .map f [] = []
  Functor:List .map f (x :: xs) = f x :: map f xs
