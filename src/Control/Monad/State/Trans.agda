{-# OPTIONS --type-in-type #-}

module Control.Monad.State.Trans where

open import Prelude

open import Control.Monad.State.Class
open import Control.Monad.Trans.Class

private
  variable
    A B S : Set
    M N : Set -> Set

record StateT (S : Set) (M : Set -> Set) (A : Set) : Set where
  constructor stateT:
  field runStateT : S -> M (Tuple A S)

open StateT public

evalStateT : {{_ : Monad M}} -> StateT S M A -> S -> M A
evalStateT (stateT: m) s = do
  (a , _) <- m s
  return a

execStateT : {{_ : Monad M}} -> StateT S M A -> S -> M S
execStateT (stateT: m) s₀ = do
  (_ , s1) <- m s₀
  return s1

mapStateT : (M (Tuple A S) -> N (Tuple B S)) -> StateT S M A -> StateT S N B
mapStateT f (stateT: m) = stateT: (f ∘ m)

withStateT : (S -> S) -> StateT S M A -> StateT S M A
withStateT f (stateT: m) = stateT: (m ∘ f)

instance
  functorStateT : {{_ : Functor M}} -> Functor (StateT S M)
  functorStateT .map f (stateT: m) = stateT: λ s₀ -> map (first f) (m s₀)

  applicativeStateT : {{_ : Monad M}} -> Applicative (StateT S M)
  applicativeStateT .pure a = stateT: λ s -> return (a , s)
  applicativeStateT ._<*>_ (stateT: mf) (stateT: mx) = stateT: λ s₀ -> do
      (f , s1) <- mf s₀
      (x , s2) <- mx s1
      return (f x , s2)

  alternativeStateT : {{_ : Alternative M}} {{_ : Monad M}} ->
    Alternative (StateT S M)
  alternativeStateT .empty = stateT: (const empty)
  alternativeStateT ._<|>_ (stateT: m) (stateT: n) = stateT: λ s ->
    m s <|> n s

  monadStateT : {{_ : Monad M}} -> Monad (StateT S M)
  monadStateT ._>>=_ (stateT: m) k = stateT: λ s₀ -> do
    (a , s1) <- m s₀
    runStateT (k a) s1

  monadTransStateT : MonadTrans (StateT S)
  monadTransStateT .lift m = stateT: λ s -> do
    a <- m
    return (a , s)
  monadTransStateT .transform = monadStateT

  monadStateStateT : {{_ : Monad M}} -> MonadState S (StateT S M)
  monadStateStateT .get = stateT: (return ∘ dupe)
  monadStateStateT .put s = stateT: (const (return (unit , s)))
