{-# OPTIONS --type-in-type #-}

module Control.Monad.Trans.State where

open import Control.Monad.Trans.Class
open import Data.Functor.Id
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

  state : (S -> Pair A S) -> M A
  state f = do
    s0 <- get
    let (a , s1) = f s0
    put s1
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
  constructor toStateT
  field
    fromStateT : S -> M (Pair A S)

open StateT public

evalStateT : {{_ : Monad M}} -> StateT S M A -> S -> M A
evalStateT m s = do
  (a , _) <- fromStateT m s
  return a

execStateT : {{_ : Monad M}} -> StateT S M A -> S -> M S
execStateT m s0 = do
  (_ , s1) <- fromStateT m s0
  return s1

mapStateT : (M (Pair A S) -> N (Pair B S)) -> StateT S M A -> StateT S N B
mapStateT f m = toStateT $ f <<< fromStateT m

withStateT : (S -> S) -> StateT S M A -> StateT S M A
withStateT f m = toStateT $ fromStateT m <<< f

instance
  functorStateT : {{_ : Functor M}} -> Functor (StateT S M)
  functorStateT .map f m = toStateT $ \ s0 ->
    map (\ where (a , s) -> (f a , s)) $ fromStateT m s0

  applicativeStateT : {{_ : Monad M}} -> Applicative (StateT S M)
  applicativeStateT = \ where
    .pure a -> toStateT $ \ s -> return (a , s)
    ._<*>_ (toStateT mf) (toStateT mx) -> toStateT $ \ s0 -> do
      (f , s1) <- mf s0
      (x , s2) <- mx s1
      return (f x , s2)

  monadStateT : {{_ : Monad M}} -> Monad (StateT S M)
  monadStateT ._>>=_ m k = toStateT $ \ s0 -> do
    (a , s1) <- fromStateT m s0
    fromStateT (k a) s1

  monadTransStateT : MonadTrans (StateT S)
  monadTransStateT = \ where
    .lift m -> toStateT \ s -> do
      a <- m
      return (a , s)
    .transform -> monadStateT

--------------------------------------------------------------------------------
-- State
--------------------------------------------------------------------------------

State : Set -> Set -> Set
State S = StateT S Id

toState : (S -> Pair A S) -> State S A
toState t = toStateT (t >>> toId)

fromState : State S A -> S -> Pair A S
fromState m = fromId <<< fromStateT m

evalState : State S A -> S -> A
evalState m s = fst (fromState m s)

execState : State S A -> S -> S
execState m s = snd (fromState m s)

mapState : (Pair A S -> Pair B S) -> State S A -> State S B
mapState = mapStateT <<< map

withState : (S -> S) -> State S ~> State S
withState f = withStateT f
