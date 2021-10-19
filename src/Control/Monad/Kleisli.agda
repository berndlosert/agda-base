{-# OPTIONS --type-in-type #-}

module Control.Monad.Kleisli where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set
    m : Set -> Set

-------------------------------------------------------------------------------
-- Triple
-------------------------------------------------------------------------------

record Triple (m : Set -> Set) : Set where
  field
    joinMap : (a -> m b) -> m a -> m b
    return : a -> m a

  bind : m a -> (a -> m b) -> m b
  bind = flip joinMap

  liftM : (a -> b) -> m a -> m b
  liftM f = joinMap (f >>> return)

  ap : m (a -> b) -> m a -> m b
  ap mf mx = joinMap (\ f -> liftM f mx) mf

open Triple {{...}} public

-------------------------------------------------------------------------------
-- Kleisli
-------------------------------------------------------------------------------

record Kleisli (m : Set -> Set) (a b : Set) : Set where
  constructor aKleisli
  field runKleisli : a -> m b

open Kleisli public

instance
  Semigroupoid-Kleisli : {{Monad m}} -> Semigroupoid (Kleisli m)
  Semigroupoid-Kleisli ._<<<_ g f = aKleisli (runKleisli g <=< runKleisli f)

  Category-Kleisli : {{Monad m}} -> Category (Kleisli m)
  Category-Kleisli .id = aKleisli \ x -> pure x
