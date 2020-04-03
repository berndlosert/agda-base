{-# OPTIONS --type-in-type #-}

module Control.Monad.Trans.State where

open import Control.Monad.Trans.Class
open import Prelude

private
  variable
    A B S : Set
    M N : Set -> Set

--------------------------------------------------------------------------------
-- MonadState
--------------------------------------------------------------------------------

record MonadState (S : Set) (M : Set -> Set) : Set where
  field
    {{monad}} : Monad M
    get : M S
    put : S -> M Unit

  state : (S -> A * S) -> M A
  state f = do
    s <- get
    let (a , s') = f s
    put s'
    return a

  modify : (S -> S) -> M Unit
  modify f = state $ (\ s -> (unit , f s))

  gets : (S -> A) -> M A
  gets f = do
    s <- get
    return (f s)

--------------------------------------------------------------------------------
-- StateT
--------------------------------------------------------------------------------

record StateT (S : Set) (M : Set -> Set) (A : Set) : Set where
  constructor stateT
  field
    runStateT : S -> M (A * S)

open StateT public

evalStateT : {{_ : Monad M}} -> StateT S M A -> S -> M A
evalStateT m s = do
  (a , _) <- runStateT m s
  return a

execStateT : {{_ : Monad M}} -> StateT S M A -> S -> M S
execStateT m s = do
  (_ , s') <- runStateT m s
  return s'

mapStateT : (M (A * S) -> N (B * S)) -> StateT S M A -> StateT S N B
mapStateT f m = stateT $ f <<< runStateT m

withStateT : (S -> S) -> StateT S M A -> StateT S M A
withStateT f m = stateT $ runStateT m <<< f

instance
  functorStateT : {{_ : Functor M}} -> Functor (StateT S M)
  functorStateT .map f m = stateT $ \ s ->
    map (\ where (a , s') -> (f a , s')) $ runStateT m s

  applicativeStateT : {{_ : Monad M}} -> Applicative (StateT S M)
  applicativeStateT = \ where
    .pure a -> stateT $ \ s -> return (a , s)
    ._<*>_ (stateT mf) (stateT mx) -> stateT $ \ s -> do
      (f , s') <- mf s
      (x , s'') <- mx s'
      return (f x , s'')

  monadStateT : {{_ : Monad M}} -> Monad (StateT S M)
  monadStateT ._>>=_ m k = stateT $ \ s -> do
    (a , s') <- runStateT m s
    runStateT (k a) s'

  monadTransStateT : MonadTrans (StateT S)
  monadTransStateT = \ where
    .lift m -> stateT \ s -> do
      a <- m
      return (a , s)
    .transform -> monadStateT

--------------------------------------------------------------------------------
-- State
--------------------------------------------------------------------------------

State : Set -> Set -> Set
State S = StateT S Identity

runState : State S A -> S -> A * S
runState m = fromIdentity <<< runStateT m

evalState : State S A -> S -> A
evalState m s = fst (runState m s)

execState : State S A -> S -> S
execState m s = snd (runState m s)

mapState : (A * S -> B * S) -> State S A -> State S B
mapState = mapStateT <<< map

withState : (S -> S) -> State S ~> State S
withState f = withStateT f
