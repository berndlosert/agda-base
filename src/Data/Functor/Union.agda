{-# OPTIONS --type-in-type #-}

module Data.Functor.Union where

open import Data.List public
open import Data.Either public
open import Data.Void public

-- Open union of functions of type Set → Set.
Union : List (Set → Set) → Set → Set
Union [] X = Void
Union (F :: Fs) X = F X + Union Fs X

open import Control.Category
open import Data.Functor

-- Union [] is a trivially a functor.
Functor:EmptyUnion : Endofunctor Sets (Union [])
Functor:EmptyUnion .map f ()

-- Union (F :: Fs) is a functor whenever F and Union Fs are.
Functor:NonemptyUnion : {F : Set → Set} {{_ : Endofunctor Sets F}}
  → {Fs : List (Set → Set)} {{_ : Endofunctor Sets (Union Fs)}}
  → Endofunctor Sets (Union (F :: Fs))
Functor:NonemptyUnion .map f (left x) = left (map f x)
Functor:NonemptyUnion .map f (right u) = right (map f u)
