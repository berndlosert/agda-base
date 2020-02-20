{-# OPTIONS --type-in-type #-}

module Data.List.Foldable where

open import Data.Foldable public
open import Data.List.Base
open import Data.Monoid

instance
  Foldable:List : Foldable List
  Foldable:List .foldMap f [] = mempty
  Foldable:List .foldMap f (x :: xs) = f x <> foldMap f xs
