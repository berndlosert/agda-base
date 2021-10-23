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
-- KleisliTriple
-------------------------------------------------------------------------------

record KleisliTriple (m : Set -> Set) : Set where
  field
    flatMap : (a -> m b) -> m a -> m b
    return : a -> m a

  flatten : m (m a) -> m a
  flatten = flatMap id

  bind : m a -> (a -> m b) -> m b
  bind = flip flatMap

  liftM : (a -> b) -> m a -> m b
  liftM f = flatMap (f >>> return)

  ap : m (a -> b) -> m a -> m b
  ap mf mx = flatMap (\ f -> liftM f mx) mf

open KleisliTriple {{...}} public

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
