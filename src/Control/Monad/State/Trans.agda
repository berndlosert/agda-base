{-# OPTIONS --type-in-type #-}

module Control.Monad.State.Trans where

open import Prelude

open import Control.Monad.Morph public
open import Control.Monad.State.Class public
open import Control.Monad.Trans.Class public

private
  variable
    a b s : Set
    m n : Set -> Set

record StateT (s : Set) (m : Set -> Set) (a : Set) : Set where
  constructor StateT:
  field runStateT : s -> m (a * s)

open StateT public

evalStateT : {{_ : Monad m}} -> StateT s m a -> s -> m a
evalStateT (StateT: m) s = do
  (a , _) <- m s
  return a

execStateT : {{_ : Monad m}} -> StateT s m a -> s -> m s
execStateT (StateT: m) s0 = do
  (_ , s1) <- m s0
  return s1

mapStateT : (m (a * s) -> n (b * s)) -> StateT s m a -> StateT s n b
mapStateT f (StateT: m) = StateT: (f ∘ m)

withStateT : (s -> s) -> StateT s m a -> StateT s m a
withStateT f (StateT: m) = StateT: (m ∘ f)

instance
  functorStateT : {{_ : Functor m}} -> Functor (StateT s m)
  functorStateT .map f (StateT: m) = StateT: λ s0 -> map (first f) (m s0)

  applicativeStateT : {{_ : Monad m}} -> Applicative (StateT s m)
  applicativeStateT .pure a = StateT: λ s -> return (a , s)
  applicativeStateT ._<*>_ (StateT: f) (StateT: x) = StateT: λ s0 -> do
      (g , s1) <- f s0
      (y , s2) <- x s1
      return (g y , s2)

  alternativeStateT : {{_ : Alternative m}} {{_ : Monad m}} ->
    Alternative (StateT s m)
  alternativeStateT .empty = StateT: (const empty)
  alternativeStateT ._<|>_ (StateT: m) (StateT: n) = StateT: λ s ->
    m s <|> n s

  monadStateT : {{_ : Monad m}} -> Monad (StateT s m)
  monadStateT ._>>=_ (StateT: m) k = StateT: λ s0 -> do
    (a , s1) <- m s0
    runStateT (k a) s1

  mfunctorStateT : MFunctor (StateT s)
  mfunctorStateT .hoist f = mapStateT f

  monadTransStateT : MonadTrans (StateT s)
  monadTransStateT .lift m = StateT: λ s -> do
    a <- m
    return (a , s)

  monadStateStateT : {{_ : Monad m}} -> MonadState s (StateT s m)
  monadStateStateT .get = StateT: (return ∘ dupe)
  monadStateStateT .put s = StateT: (const (return (unit , s)))
