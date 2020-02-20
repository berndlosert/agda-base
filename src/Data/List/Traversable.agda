{-# OPTIONS --type-in-type #-}

module Data.List.Traversable where

open import Control.Applicative
open import Data.List.Base
open import Data.List.Foldable
open import Data.List.Functor
open import Data.Traversable public

instance
  Traversable:List : Traversable List
  Traversable:List .sequence {F} {X} = foldr cons (pure [])
    where
      cons : F X -> F (List X) -> F (List X)
      cons x xs = (| _::_ x xs |)
