{-# OPTIONS --type-in-type #-}

module Control.Monad.StateT where

open import Prelude

private
  variable
    A B S : Set
    M N : Set -> Set

record StateT (S : Set) (M : Set -> Set) (A : Set) : Set where
  constructor StateT:
  field
    run : S -> M (A * S)

eval : {{_ : Monad M}} -> StateT S M A -> S -> M A
eval m s = do
  Pair: a _ <- StateT.run m s
  return a

exec : {{_ : Monad M}} -> StateT S M A -> S -> M S
exec m s = do
  Pair: _ s' <- StateT.run m s
  return s'

map' : (M (A * S) -> N (B * S)) -> StateT S M A -> StateT S N B
map' f m = StateT: $ f <<< StateT.run m

with' : (S -> S) -> StateT S M A -> StateT S M A
with' f m = StateT: $ StateT.run m <<< f

instance
  Functor:StateT : {{_ : Functor M}} -> Functor (StateT S M)
  Functor:StateT .map f m = StateT: $ \ s ->
    map (\ where (Pair: a s') -> Pair: (f a) s') $ StateT.run m s

  Applicative:StateT : {{_ : Monad M}} -> Applicative (StateT S M)
  Applicative:StateT = \ where
    .pure a -> StateT: $ \ s -> return (Pair: a s)
    ._<*>_ (StateT: mf) (StateT: mx) -> StateT: $ \ s -> do
      (Pair: f s') <- mf s
      (Pair: x s'') <- mx s'
      return (Pair: (f x) s'')
