module Data.Traversable where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Applicative.Backwards using (forwards; backwards)
open import Control.Monad using (Monad)
open import Control.Monad.Instances using (Monad-Identity)
open import Control.Monad.State using (runState; state; runStateT; asStateT)
open import Data.Monoid.Foldable using (Foldable)
open import Data.Monoid.Reverse using (Reverse; reverse; getReverse)

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b s : Type
    f m t : Type -> Type

-------------------------------------------------------------------------------
-- Traversable
-------------------------------------------------------------------------------

record Traversable (t : Type -> Type) : Type where
  field
    overlap {{Functor-super}} : Functor t
    overlap {{Foldable-super}} : Foldable t
    traverse : {{Applicative f}} -> (a -> f b) -> t a -> f (t b)

open Traversable {{...}} public

module _ {{_ : Traversable t}} where
  sequence : {{Applicative f}} -> t (f a) -> f (t a)
  sequence = traverse id

  for : {{Applicative f}} -> t a -> (a -> f b) -> f (t b)
  for = flip traverse

instance
  Traversable-Identity : Traversable Identity
  Traversable-Identity .traverse f x = asIdentity <$> f (runIdentity x)

  Traversable-Maybe : Traversable Maybe
  Traversable-Maybe .traverse f = \ where
    nothing -> (| nothing |)
    (just x) -> (| just (f x) |)

  Traversable-List : Traversable List
  Traversable-List .traverse f = \ where
    [] -> (| [] |)
    (x :: xs) -> (| f x :: traverse f xs |)

  Traversable-Reverse : {{Traversable f}} -> Traversable (Reverse f)
  Traversable-Reverse .traverse f (reverse x) =
    map reverse <<< forwards $ traverse (backwards <<< f) x

-------------------------------------------------------------------------------
-- mapAccumL, mapAccumR, mapAccumM
-------------------------------------------------------------------------------

mapAccumL : {{Traversable t}} -> (s -> a -> Tuple s b) -> s -> t a -> Tuple s (t b)
mapAccumL f s bs = flip runState s (for bs (state <<< flip f))

mapAccumR : {{Traversable t}} -> (s -> a -> Tuple s b) -> s -> t a -> Tuple s (t b)
mapAccumR f s = map getReverse <<< mapAccumL f s <<< reverse

mapAccumM : {{Traversable t}} -> {{Monad m}}
  -> (s -> a -> m (Tuple s b)) -> s -> t a -> m (Tuple s (t b))
mapAccumM f s t = runStateT (traverse (asStateT <<< flip f) t) s