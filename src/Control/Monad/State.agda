{-# OPTIONS --type-in-type #-}

module Control.Monad.State where

open import Prelude

open import Control.Monad.State.Trans

open Control.Monad.State.Trans public
  using (functorStateT; applicativeStateT; monadStateT)

private variable A B S : Set

State : Set -> Set -> Set
State S = StateT S Identity

state : (S -> A * S) -> State S A
state t = stateT: (identity: ∘ t)

runState : State S A -> S -> A * S
runState m = runIdentity ∘ runStateT m

evalState : State S A -> S -> A
evalState m s = fst (runState m s)

execState : State S A -> S -> S
execState m s = snd (runState m s)

mapState : (A * S -> B * S) -> State S A -> State S B
mapState = mapStateT ∘ map

withState : (S -> S) -> State S ~> State S
withState f = withStateT f
