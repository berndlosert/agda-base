module Control.Monad.State where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.State.Class
open import Control.Monad.State.Trans

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
    a b s : Type

-------------------------------------------------------------------------------
-- State
-------------------------------------------------------------------------------

State : Type -> Type -> Type
State s = StateT s Identity

{-# DISPLAY StateT s Identity = State s #-}

runState : State s a -> s -> Tuple s a
runState m = runIdentity <<< runStateT m

evalState : State s a -> s -> a
evalState m = runIdentity <<< evalStateT m

execState : State s a -> s -> s
execState m = runIdentity <<< execStateT m

mapState : (Tuple s a -> Tuple s b) -> State s a -> State s b
mapState = mapStateT <<< map

withState : (s -> s) -> State s a -> State s a
withState = withStateT
