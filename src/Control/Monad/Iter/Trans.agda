{-# OPTIONS --type-in-type #-}

module Control.Monad.Iter.Trans where

open import Prelude

open import Control.Monad.Free.Class
open import Control.Monad.State.Class
open import Control.Monad.Trans.Class
open import Control.Size

private
  variable
    a b r s : Set
    f m : Set -> Set

data IterF (a r : Set) : Set where
  Break : a -> IterF a r
  Continue : r -> IterF a r

record IterT (m : Set -> Set) (a : Set) : Set where
  coinductive
  field runIterT : IterF a (IterT m a)

open IterT public

Iter : Set -> Set
Iter = IterT Identity

delay : {{_ : Monad m}} -> IterT m a -> IterT m a
runIterT (delay iter) = Continue iter

never : {{_ : Monad m}} -> IterT m a
runIterT never = Continue never

-- N.B. This should only be called if you're sure that the IterT m a value
-- terminates. If it doesn't terminate, this will loop forever.
{-# TERMINATING #-}
unsafeRetract : {{_ : Monad m}} -> IterT m a -> m a
unsafeRetract iter with (runIterT iter)
... | Break x = return x
... | Continue iter' = unsafeRetract iter'

instance
  functorIterF : Functor (IterF a)
  functorIterF .map f (Break a) = Break a
  functorIterF .map f (Continue r) = Continue (f r)

  functorIterT : {{_ : Monad m}} -> Functor (IterT m)
  functorIterT .map f iter with runIterT iter
  ... | Break x = λ where .runIterT -> Break (f x)
  ... | Continue iter' = λ where .runIterT -> Continue $ map f iter'

  applicativeIterT : {{_ : Monad m}} -> Applicative (IterT m)
  applicativeIterT .pure x = λ where .runIterT -> Break x
  applicativeIterT ._<*>_ iter x with runIterT iter
  ... | Break f = map f x
  ... | Continue iter' = λ where .runIterT -> Continue $ iter' <*> x

  monadIterT : {{_ : Monad m}} -> Monad (IterT m)
  monadIterT ._>>=_ iter k with runIterT iter
  ... | Break m = k m
  ... | Continue iter' = λ where .runIterT -> Continue $ iter' >>= k

  alternativeIterT : {{_ : Monad m}} -> Alternative (IterT m)
  alternativeIterT .empty = never
  alternativeIterT ._<|>_ l r with runIterT l
  ... | Break x = l
  ... | Continue iter' =
    case runIterT r of λ where
      (Break y) -> r
      (Continue iter'') -> λ where .runIterT -> Continue $ iter' <|> iter''

{-
  monadFreeIterT : {{_ : Monad m}} -> MonadFree Identity (IterT m)
  monadFreeIterT .wrap = IterT: ∘ return ∘ Right ∘ runIdentity

  monadTransIterT : MonadTrans (IterT i)
  monadTransIterT .lift = IterT: ∘ map Left

  monadStateIterT : {{_ : MonadState s m}} -> MonadState s (IterT i m)
  monadStateIterT .get = lift get
  monadStateIterT .put s = lift (put s)
-}
