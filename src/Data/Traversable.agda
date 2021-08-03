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
    a b c : Type
    f t : Type -> Type

-------------------------------------------------------------------------------
-- Traversable
-------------------------------------------------------------------------------

record Traversable (t : Type -> Type) : Type where
  field
    overlap {{Functor-super}} : Functor t
    overlap {{Foldable-super}} : Foldable t
    traverse : {{Applicative f}} -> (a -> f b) -> t a -> f (t b)

  sequence : {{Applicative f}} -> t (f a) -> f (t a)
  sequence = traverse id

  for : {{Applicative f}} -> t a -> (a -> f b) -> f (t b)
  for = flip traverse

open Traversable {{...}} public

instance
  Traversable-Maybe : Traversable Maybe
  Traversable-Maybe .traverse f = \ where
    Nothing -> (| Nothing |)
    (Just x) -> (| Just (f x) |)

  Traversable-List : Traversable List
  Traversable-List .traverse f = \ where
    [] -> (| [] |)
    (x :: xs) -> (| _::_ (f x) (traverse f xs) |)

  Traversable-Reverse : {{Traversable f}} -> Traversable (Reverse f)
  Traversable-Reverse .traverse f (Reverse: x) =
    map Reverse: <<< forwards $ traverse (Backwards: <<< f) x

-------------------------------------------------------------------------------
-- mapAccumL, mapAccumR
-------------------------------------------------------------------------------

mapAccumL : {{Traversable t}} -> (a -> b -> a * c) -> a -> t b -> a * t c
mapAccumL f z bs = swap $ flip runState z $ for bs \ b ->
  state (flip f b >>> swap)

mapAccumR : {{Traversable t}} -> (a -> b -> a * c) -> a -> t b -> a * t c
mapAccumR f z = map getReverse <<< mapAccumL f z <<< Reverse:
