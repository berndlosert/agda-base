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

{-# NO_POSITIVITY_CHECK #-}
record IterT (m : Set -> Set) (a : Set) : Set where
  coinductive
  field runIterT : m (a + IterT m a)

open IterT public

Iter : Set -> Set
Iter = IterT Identity

delay : {{_ : Monad m}} -> IterT m a -> IterT m a
delay iter .runIterT = return (Right iter)

{-# NON_TERMINATING #-}
never : {{_ : Monad m}} -> IterT m a
never .runIterT = return (Right never)

-- N.B. This should only be called if you're sure that the IterT m a value
-- terminates. If it doesn't terminate, this will loop forever.
{-# TERMINATING #-}
unsafeRetract : {{_ : Monad m}} -> IterT m a -> m a
unsafeRetract iter = runIterT iter >>= either return unsafeRetract

instance
  {-# TERMINATING #-}
  functorIterT : {{_ : Monad m}} -> Functor (IterT m)
  functorIterT .map f iter .runIterT =
    runIterT iter >>= return ∘ bimap f (map f)

  {-# TERMINATING #-}
  applicativeIterT : {{_ : Monad m}} -> Applicative (IterT m)
  applicativeIterT .pure x .runIterT = return (Left x)
  applicativeIterT ._<*>_ iter x .runIterT =
    runIterT iter >>= either (runIterT ∘ (_<$> x)) (return ∘ Right ∘ (_<*> x))

  {-# TERMINATING #-}
  monadIterT : {{_ : Monad m}} -> Monad (IterT m)
  monadIterT ._>>=_ iter k .runIterT = do
    result <- runIterT iter
    case result of λ where
      (Left m) -> runIterT (k m)
      (Right iter') -> return $ Right $ iter' >>= k

  {-# TERMINATING #-}
  alternativeIterT : {{_ : Monad m}} -> Alternative (IterT m)
  alternativeIterT .empty = never
  alternativeIterT ._<|>_ l r .runIterT = do
    resultl <- runIterT l
    case resultl of λ where
      (Left x) -> runIterT l
      (Right iter') -> do
        resultr <- runIterT r
        case resultr of λ where
          (Left y) -> runIterT r
          (Right iter'') -> return $ Right $ iter' <|> iter''

  --monadFreeIterT : {{_ : Monad m}} -> MonadFree Identity (IterT m)
  --monadFreeIterT .wrap .runIterT = return ∘ Right ∘ runIdentity

  --monadTransIterT : MonadTrans IterT
  --monadTransIterT .lift .runIterT = map Left

  --monadStateIterT : {{_ : MonadState s m}} -> MonadState s (IterT m)
  --monadStateIterT .get = lift get
  --monadStateIterT .put s = lift (put s)

