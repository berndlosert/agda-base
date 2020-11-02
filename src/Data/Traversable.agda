{-# OPTIONS --type-in-type #-}

module Data.Traversable where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Applicative.Backwards
open import Control.Monad.State
open import Data.Foldable
open import Data.Foldable.Reverse

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Set
    f t : Set -> Set

-------------------------------------------------------------------------------
-- Traversable
-------------------------------------------------------------------------------

record Traversable (t : Set -> Set) : Set where
  field
    overlap {{Functor-super}} : Functor t
    overlap {{Foldable-super}} : Foldable t
    traverse : {{_ : Applicative f}} -> (a -> f b) -> t a -> f (t b)

  sequence : {{_ : Applicative f}} -> t (f a) -> f (t a)
  sequence = traverse id

  for : {{_ : Applicative f}} -> t a -> (a -> f b) -> f (t b)
  for = flip traverse

open Traversable {{...}} public

instance
  Traversable-Maybe : Traversable Maybe
  Traversable-Maybe .traverse f m with m
  ... | Nothing = pure Nothing
  ... | Just x = (| Just (f x) |)

  Traversable-List : Traversable List
  Traversable-List .traverse f l with l
  ... | [] = pure []
  ... | x :: xs = (| _::_ (f x) (traverse f xs) |)

  Traversable-Reverse : {{_ : Traversable f}} -> Traversable (Reverse f)
  Traversable-Reverse .traverse f (Reverse: x) =
    map Reverse: <<< forwards $ traverse (Backwards: <<< f) x

-------------------------------------------------------------------------------
-- mapAccumL, mapAccumR
-------------------------------------------------------------------------------

mapAccumL : {{_ : Traversable t}} -> (a -> b -> a * c) -> a -> t b -> a * t c
mapAccumL f z bs = swap $ flip runState z $ for bs \ b ->
  state (flip f b >>> swap)

mapAccumR : {{_ : Traversable t}} -> (a -> b -> a * c) -> a -> t b -> a * t c
mapAccumR f z = map getReverse <<< mapAccumL f z <<< Reverse:
