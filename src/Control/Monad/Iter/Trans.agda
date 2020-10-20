{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-positivity-check #-}
{-# OPTIONS --no-termination-check #-}

module Control.Monad.Iter.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Free.Class
open import Control.Monad.State.Class
open import Control.Monad.Trans.Class
open import Data.Functor.Identity

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a s : Set
    m : Set -> Set

-------------------------------------------------------------------------------
-- IterT
-------------------------------------------------------------------------------

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
retract : {{_ : Monad m}} -> IterT m a -> m a
retract iter = runIterT iter >>= either return retract

instance
  Functor-IterT : {{_ : Monad m}} -> Functor (IterT m)
  Functor-IterT .map f iter .runIterT =
    runIterT iter >>= bimap f (map f) >>> return

  Applicative-IterT : {{_ : Monad m}} -> Applicative (IterT m)
  Applicative-IterT .pure x .runIterT = return (Left x)
  Applicative-IterT ._<*>_ iter x .runIterT = do
    result <- runIterT iter
    case result of \ where
      (Left f) -> runIterT (map f x)
      (Right iter') -> return (Right (iter' <*> x))

  Monad-IterT : {{_ : Monad m}} -> Monad (IterT m)
  Monad-IterT ._>>=_ iter k .runIterT = do
    result <- runIterT iter
    case result of \ where
      (Left m) -> runIterT (k m)
      (Right iter') -> return (Right (iter' >>= k))

  Alternative-IterT : {{_ : Monad m}} -> Alternative (IterT m)
  Alternative-IterT .empty = never
  Alternative-IterT ._<|>_ l r .runIterT = do
    resultl <- runIterT l
    case resultl of \ where
      (Left _) -> return resultl
      (Right iter') -> do
        resultr <- runIterT r
        case resultr of \ where
          (Left _) -> return resultr
          (Right iter'') -> return (Right (iter' <|> iter''))

  MonadFree-IterT : {{_ : Monad m}} -> MonadFree Identity (IterT m)
  MonadFree-IterT .wrap (Identity: iter) = delay iter

  MonadTrans-IterT : MonadTrans IterT
  MonadTrans-IterT .lift m .runIterT = map Left m

  MonadState-IterT : {{_ : MonadState s m}} -> MonadState s (IterT m)
  MonadState-IterT .state m = lift (state m)
