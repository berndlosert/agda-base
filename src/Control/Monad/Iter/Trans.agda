module Control.Monad.Iter.Trans where

open import Prelude

open import Control.Monad.Free.Class
open import Control.Monad.State.Class
open import Control.Monad.Trans.Class

private
  variable
    a s : Set
    m : Set -> Set

record IterT (m : Set -> Set) (a : Set) : Set where
  coinductive
  field runIterT : m (a + IterT m a)

open IterT public

Iter : Set -> Set
Iter = IterT Identity

delay : {{_ : Monad m}} -> IterT m a -> IterT m a
delay iter .runIterT = return (Right iter)

never : {{_ : Monad m}} -> IterT m a
never .runIterT = return (Right never)

-- N.B. This should only be called if you're sure that the IterT m a value
-- terminates. If it doesn't terminate, this will loop forever.
unsafeRetract : {{_ : Monad m}} -> IterT m a -> m a
unsafeRetract iter = runIterT iter >>= either return unsafeRetract

instance
  functorIterT : {{_ : Monad m}} -> Functor (IterT m)
  functorIterT .map f iter .runIterT =
    runIterT iter >>= return ∘ bimap f (map f)

  applicativeIterT : {{_ : Monad m}} -> Applicative (IterT m)
  applicativeIterT .pure x .runIterT = return (Left x)
  applicativeIterT ._<*>_ iter x .runIterT = do
    result <- runIterT iter
    case result of λ where
      (Left f) -> runIterT (f <$> x)
      (Right iter') -> return $ Right $ iter' <*> x

  monadIterT : {{_ : Monad m}} -> Monad (IterT m)
  monadIterT ._>>=_ iter k .runIterT = do
    result <- runIterT iter
    case result of λ where
      (Left m) -> runIterT (k m)
      (Right iter') -> return $ Right $ iter' >>= k

  alternativeIterT : {{_ : Monad m}} -> Alternative (IterT m)
  alternativeIterT .empty = never
  alternativeIterT ._<|>_ l r .runIterT = do
    resultl <- runIterT l
    case resultl of λ where
      (Left _) -> return resultl
      (Right iter') -> do
        resultr <- runIterT r
        case resultr of λ where
          (Left _) -> return resultr
          (Right iter'') -> return $ Right $ iter' <|> iter''

  monadFreeIterT : {{_ : Monad m}} -> MonadFree Identity (IterT m)
  monadFreeIterT .wrap (Identity: iter) = delay iter

  monadTransIterT : MonadTrans IterT
  monadTransIterT .lift m .runIterT = map Left m

  monadStateIterT : {{_ : MonadState s m}} -> MonadState s (IterT m)
  monadStateIterT .get = lift get
  monadStateIterT .put s = lift (put s)
