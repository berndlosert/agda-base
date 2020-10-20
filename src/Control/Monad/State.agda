{-# OPTIONS --type-in-type #-}

module Control.Monad.State where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.State.Class
open import Control.Monad.State.Trans
open import Data.Functor.Identity

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.State.Class public
open Control.Monad.State.Trans public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b s : Set

-------------------------------------------------------------------------------
-- State
-------------------------------------------------------------------------------

State : Set -> Set -> Set
State s = StateT s Identity

runState : State s a -> s -> a * s
runState m = runIdentity <<< runStateT m

evalState : State s a -> s -> a
evalState m s = fst (runState m s)

execState : State s a -> s -> s
execState m s = snd (runState m s)

mapState : (a * s -> b * s) -> State s a -> State s b
mapState = mapStateT <<< map

withState : (s -> s) -> State s a -> State s a
withState f = withStateT f
