{-# OPTIONS --type-in-type #-}

module Data.Stream.Base where

-- Stream X represents infinite lists of elements of X.

record Stream (X : Set) : Set where
  coinductive
  field
    head : X
    tail : Stream X

open Stream public

-- Stream forms a functor.

open import Data.Functor public

instance
  Functor:Stream : Endofunctor Sets Stream
  Functor:Stream .map f xs .head = f (head xs)
  Functor:Stream .map f xs .tail = map f (tail xs)

-- Stream forms an applicative.

open import Control.Applicative public

instance
  Applicative:Stream : Applicative Stream
  Applicative:Stream .pure x .head = x
  Applicative:Stream .pure x .tail = pure x
  Applicative:Stream ._<*>_ fs xs .head = head fs (head xs)
  Applicative:Stream ._<*>_ fs xs .tail = tail fs <*> tail xs

-- Stream forms a comonad.

open import Control.Comonad public

instance
  Comonad:Stream : Comonad Sets Stream
  Comonad:Stream .coextend f xs = pure (f xs)
  Comonad:Stream .extract xs = head xs
