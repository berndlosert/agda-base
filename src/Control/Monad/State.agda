{-# OPTIONS --type-in-type #-}

module Control.Monad.State where

open import Prelude

open import Control.Monad.State.Trans

open Control.Monad.State.Trans public
  using (functorStateT; applicativeStateT; monadStateT)

private variable a b s : Set

State : Set -> Set -> Set
State s = StateT s Identity

state : (s -> a * s) -> State s a
state t = StateT: (Identity: ∘ t)

runState : State s a -> s -> a * s
runState m = runIdentity ∘ runStateT m

evalState : State s a -> s -> a
evalState m s = fst (runState m s)

execState : State s a -> s -> s
execState m s = snd (runState m s)

mapState : (a * s -> b * s) -> State s a -> State s b
mapState = mapStateT ∘ map

withState : (s -> s) -> State s ~> State s
withState f = withStateT f
