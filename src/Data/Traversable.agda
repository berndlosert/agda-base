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
    a b s : Set
    f m t : Set -> Set

-------------------------------------------------------------------------------
-- Traversable
-------------------------------------------------------------------------------

record Traversable (t : Set -> Set) : Set where
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
    nothing -> (| nothing |)
    (just x) -> (| just (f x) |)

  Traversable-List : Traversable List
  Traversable-List .traverse f = \ where
    [] -> (| [] |)
    (x :: xs) -> (| f x :: traverse f xs |)

  Traversable-Reverse : {{Traversable f}} -> Traversable (Reverse f)
  Traversable-Reverse .traverse f (aReverse x) =
    map aReverse <<< forwards $ traverse (aBackwards <<< f) x

-------------------------------------------------------------------------------
-- mapAccumL, mapAccumR, mapAccumM
-------------------------------------------------------------------------------

mapAccumL : {{Traversable t}} -> (s -> a -> Pair s b) -> s -> t a -> Pair s (t b)
mapAccumL f s bs = flip runState s $ for bs (state <<< flip f)

mapAccumR : {{Traversable t}} -> (s -> a -> Pair s b) -> s -> t a -> Pair s (t b)
mapAccumR f s = map getReverse <<< mapAccumL f s <<< aReverse

mapAccumM : {{Traversable t}} -> {{Monad m}} 
  -> (s -> a -> m (Pair s b)) -> s -> t a -> m (Pair s (t b))
mapAccumM f s t = runStateT (traverse (aStateT <<< flip f) t) s