module Control.Monad.State where

open import Prelude

open import Control.Monad.State.Class public
open import Control.Monad.State.Trans public

private variable a b s : Set

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

withState : (s -> s) -> State s ~> State s
withState f = withStateT f
