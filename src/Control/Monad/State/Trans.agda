{-# OPTIONS --type-in-type #-}

module Control.Monad.State.Trans where

open import Prelude

open import Control.Monad.Base
open import Control.Monad.Morph
open import Control.Monad.State.Class
open import Control.Monad.Trans.Class

private
  variable
    A B S : Set
    M N : Set -> Set

record StateT (S : Set) (M : Set -> Set) (A : Set) : Set where
  constructor StateT:
  field runStateT : S -> M (A * S)

open StateT public

evalStateT : {{_ : Monad M}} -> StateT S M A -> S -> M A
evalStateT (StateT: m) s = do
  (a , _) <- m s
  return a

execStateT : {{_ : Monad M}} -> StateT S M A -> S -> M S
execStateT (StateT: m) s0 = do
  (_ , s1) <- m s0
  return s1

mapStateT : (M (A * S) -> N (B * S)) -> StateT S M A -> StateT S N B
mapStateT f (StateT: m) = StateT: (f ∘ m)

withStateT : (S -> S) -> StateT S M A -> StateT S M A
withStateT f (StateT: m) = StateT: (m ∘ f)

instance
  functorStateT : {{_ : Functor M}} -> Functor (StateT S M)
  functorStateT .map f (StateT: m) = StateT: λ s0 -> map (first f) (m s0)

  applicativeStateT : {{_ : Monad M}} -> Applicative (StateT S M)
  applicativeStateT .pure a = StateT: λ s -> return (a , s)
  applicativeStateT ._<*>_ (StateT: f) (StateT: x) = StateT: λ s0 -> do
      (g , s1) <- f s0
      (y , s2) <- x s1
      return (g y , s2)

  alternativeStateT : {{_ : Alternative M}} {{_ : Monad M}} ->
    Alternative (StateT S M)
  alternativeStateT .empty = StateT: (const empty)
  alternativeStateT ._<|>_ (StateT: m) (StateT: n) = StateT: λ s ->
    m s <|> n s

  monadStateT : {{_ : Monad M}} -> Monad (StateT S M)
  monadStateT ._>>=_ (StateT: m) k = StateT: λ s0 -> do
    (a , s1) <- m s0
    runStateT (k a) s1

  mfunctorStateT : MFunctor (StateT S)
  mfunctorStateT .hoist f = mapStateT f

  monadTransStateT : MonadTrans (StateT S)
  monadTransStateT .lift m = StateT: λ s -> do
    a <- m
    return (a , s)
  monadTransStateT .tmap f _ = hoist f

  monadStateStateT : {{_ : Monad M}} -> MonadState S (StateT S M)
  monadStateStateT .get = StateT: (return ∘ dupe)
  monadStateStateT .put s = StateT: (const (return (unit , s)))
