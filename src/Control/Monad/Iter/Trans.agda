{-# OPTIONS --type-in-type #-}

module Control.Monad.Iter.Trans where

open import Prelude

open import Control.Monad.Free.Class
open import Control.Monad.State.Class
open import Control.Monad.Trans.Class

private
  variable
    a s : Set
    f m : Set -> Set

{-# NO_POSITIVITY_CHECK #-}
record IterT (m : Set -> Set) (a : Set) : Set where
  constructor IterT:
  field runIterT : m (a + IterT m a)

open IterT public

Iter : Set -> Set
Iter = IterT Identity

delay : {{_ : Monad f}} {{_ : MonadFree f m}} -> m a -> m a
delay = wrap ∘ return

{-# NON_TERMINATING #-}
never : {{_ : Monad f}} {{_ : MonadFree f m}} -> m a
never = delay never

{-# TERMINATING #-}
retract : {{_ : Monad m}} -> IterT m a -> m a
retract m = runIterT m >>= either return retract

instance
  {-# TERMINATING #-}
  functorIterT : {{_ : Monad m}} -> Functor (IterT m)
  applicativeIterT : {{_ : Monad m}} -> Applicative (IterT m)
  monadIterT : {{_ : Monad m}} -> Monad (IterT m)

  functorIterT .map f = IterT: ∘ map (bimap f (map f)) ∘ runIterT
  applicativeIterT .pure = IterT: ∘ return ∘ Left
  applicativeIterT ._<*>_ = ap
  monadIterT ._>>=_ (IterT: m) k = IterT: do
    result <- m
    case result of λ where
      (Left x) -> runIterT (k x)
      (Right iter) -> return $ Right (iter >>= k)

  monadFreeIterT : {{_ : Monad m}} -> MonadFree Identity (IterT m)
  monadFreeIterT .wrap = IterT: ∘ return ∘ Right ∘ runIdentity

  {-# TERMINATING #-}
  alternativeIterT : {{_ : Monad m}} -> Alternative (IterT m)
  alternativeIterT .empty = never
  alternativeIterT ._<|>_ (IterT: l) (IterT: r) = IterT: do
    result <- l
    case result of λ where
      (Left x) -> return (Left x)
      (Right iter) -> flip map r $ second $ (iter <|>_)

  monadTransIterT : MonadTrans IterT
  monadTransIterT .lift = IterT: ∘ map Left

  monadStateIterT : {{_ : MonadState s m}} -> MonadState s (IterT m)
  monadStateIterT .get = lift get
  monadStateIterT .put s = lift (put s)
