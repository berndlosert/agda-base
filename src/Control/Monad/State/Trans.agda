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
  field runStateT : S -> M (A * S)

open StateT public

evalStateT : {{_ : Monad M}} -> StateT S M A -> S -> M A
evalStateT m s = do
  (a , _) <- runStateT m s
  return a

execStateT : {{_ : Monad M}} -> StateT S M A -> S -> M S
execStateT m s₀ = do
  (_ , s1) <- runStateT m s₀
  return s1

mapStateT : (M (A * S) -> N (B * S)) -> StateT S M A -> StateT S N B
mapStateT f m = stateT: $ f ∘ runStateT m

withStateT : (S -> S) -> StateT S M A -> StateT S M A
withStateT f m = stateT: $ runStateT m ∘ f

instance
  functorStateT : {{_ : Functor M}} -> Functor (StateT S M)
  functorStateT .map f m = stateT: λ s₀ ->
    map (first f) $ runStateT m s₀

  applicativeStateT : {{_ : Monad M}} -> Applicative (StateT S M)
  applicativeStateT = λ where
    .pure a -> stateT: λ s -> return (a , s)
    ._<*>_ mf mx -> stateT: λ s₀ -> do
      (f , s1) <- runStateT mf s₀
      (x , s2) <- runStateT mx s1
      return (f x , s2)

  alternativeStateT : {{_ : Alternative M}} {{_ : Monad M}} ->
    Alternative (StateT S M)
  alternativeStateT .empty = stateT: (const empty)
  alternativeStateT ._<|>_ m n = stateT: λ s ->
    runStateT m s <|> runStateT n s

  monadStateT : {{_ : Monad M}} -> Monad (StateT S M)
  monadStateT ._>>=_ m k = stateT: λ s₀ -> do
    (a , s1) <- runStateT m s₀
    runStateT (k a) s1

  monadTransStateT : MonadTrans (StateT S)
  monadTransStateT = λ where
    .lift m -> stateT: λ s -> do
      a <- m
      return (a , s)
    .transform -> monadStateT

  monadStateStateT : {{_ : Monad M}} -> MonadState S (StateT S M)
  monadStateStateT .get = stateT: (return ∘ dupe)
  monadStateStateT .put s = stateT: (const (return (unit , s)))
