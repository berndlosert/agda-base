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

{-# NO_POSITIVITY_CHECK #-}
record IterT (m : Set -> Set) (a : Set) : Set where
  coinductive
  field runIterT : m (IterF a (IterT m a))

open IterT public

Iter : Set -> Set
Iter = IterT Identity

delay : {{_ : Monad m}} -> IterT m a -> IterT m a
delay iter = λ where .runIterT -> return (Continue iter)

{-# NON_TERMINATING #-}
never : {{_ : Monad m}} -> IterT m a
never = λ where .runIterT -> return (Continue never)

-- N.B. This should only be called if you're sure that the IterT m a value
-- terminates. If it doesn't terminate, this will loop forever.
{-# TERMINATING #-}
unsafeRetract : {{_ : Monad m}} -> IterT m a -> m a
unsafeRetract iter = do
  result <- runIterT iter
  case result of λ where
    (Break x) -> return x
    (Continue iter') -> unsafeRetract iter'

instance
  functorIterF : Functor (IterF a)
  functorIterF .map f (Break a) = Break a
  functorIterF .map f (Continue r) = Continue (f r)

  {-# TERMINATING #-}
  functorIterT : {{_ : Monad m}} -> Functor (IterT m)
  functorIterT .map f iter = λ where
    .runIterT -> do
      result <- runIterT iter
      return $ case result of λ where
        (Break x) -> Break (f x)
        (Continue iter') -> Continue (map f iter')

  {-# TERMINATING #-}
  applicativeIterT : {{_ : Monad m}} -> Applicative (IterT m)
  applicativeIterT .pure x = λ where .runIterT -> return (Break x)
  applicativeIterT ._<*>_ iter x = λ where
    .runIterT -> do
      result <- runIterT iter
      case result of λ where
        (Break f) -> runIterT (map f x)
        (Continue iter') -> return $ Continue $ iter' <*> x

  {-# TERMINATING #-}
  monadIterT : {{_ : Monad m}} -> Monad (IterT m)
  monadIterT ._>>=_ iter k = λ where
    .runIterT -> do
      result <- runIterT iter
      case result of λ where
        (Break m) -> runIterT (k m)
        (Continue iter') -> return $ Continue $ iter' >>= k

  {-# TERMINATING #-}
  alternativeIterT : {{_ : Monad m}} -> Alternative (IterT m)
  alternativeIterT .empty = never
  alternativeIterT ._<|>_ l r .runIterT = do
    resultl <- runIterT l
    case resultl of λ where
      (Break x) -> runIterT l
      (Continue iter') -> do
        resultr <- runIterT r
        case resultr of λ where
          (Break y) -> runIterT r
          (Continue iter'') -> return $ Continue $ iter' <|> iter''
{-
  monadFreeIterT : {{_ : Monad m}} -> MonadFree Identity (IterT m)
  monadFreeIterT .wrap = IterT: ∘ return ∘ Right ∘ runIdentity

  monadTransIterT : MonadTrans (IterT i)
  monadTransIterT .lift = IterT: ∘ map Left

  monadStateIterT : {{_ : MonadState s m}} -> MonadState s (IterT i m)
  monadStateIterT .get = lift get
  monadStateIterT .put s = lift (put s)
-}
