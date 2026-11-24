module Control.Comonad.Traced where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Control.Comonad
open import Control.Semigroupoid using (_<<<_)
open import Data.Functor using (Functor; map)
open import Data.Monoid using (Monoid; mempty)
open import Data.Semigroup using (_<>_)
open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    m : Type

-------------------------------------------------------------------------------
-- Traced
-------------------------------------------------------------------------------

record Traced (m a : Type) : Type where
  constructor asTraced
  field runTraced : m -> a

open Traced public

instance
  Functor-Traced : Functor (Traced m)
  Functor-Traced .map f g = asTraced (f <<< runTraced g)

  Comonad-Traced : {{Monoid m}} -> Comonad (Traced m)
  Comonad-Traced .extend h t = asTraced \ where
    m -> h (asTraced \ m1 -> runTraced t (m <> m1))
  Comonad-Traced .extract f = runTraced f mempty
