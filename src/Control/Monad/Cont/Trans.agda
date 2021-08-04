{-# OPTIONS --type-in-type #-}

module Control.Monad.Cont.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Cont.Class
open import Control.Monad.IO.Class
open import Control.Monad.Reader.Class
open import Control.Monad.State.Class
open import Control.Monad.Trans.Class

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Cont.Class public
open Control.Monad.Trans.Class public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b r r' s : Type
    f m n : Type -> Type

-------------------------------------------------------------------------------
-- ContT
-------------------------------------------------------------------------------

record ContT (r : Type) (m : Type -> Type) (a : Type) : Type where
  constructor ContT:
  field runContT : (a -> m r) -> m r

open ContT public

evalContT : {{Monad m}} -> ContT r m r -> m r
evalContT (ContT: m) = m pure

mapContT : (m r -> m r) -> ContT r m a -> ContT r m a
mapContT f (ContT: m) = ContT: (f <<< m)

withContT : ((b -> m r) -> (a -> m r)) -> ContT r m a -> ContT r m b
withContT f (ContT: m) = ContT: (m <<< f)

instance
  Functor-ContT : Functor (ContT r m)
  Functor-ContT .map f (ContT: m) = ContT: \ c -> m (c <<< f)

  Applicative-ContT : Applicative (ContT r m)
  Applicative-ContT .pure x = ContT: (\ f -> f x)
  Applicative-ContT ._<*>_ (ContT: f) (ContT: x) =
    ContT: \ c -> f \ g -> x (c <<< g)

  Monad-ContT : Monad (ContT r m)
  Monad-ContT ._>>=_ (ContT: m) k = ContT: \ c -> m \ x -> runContT (k x) c

  MonadTrans-ContT : MonadTrans (ContT r)
  MonadTrans-ContT .lift m = ContT: (m >>=_)

  MonadCont-ContT : MonadCont (ContT r m)
  MonadCont-ContT .callCC f =
    ContT: \ c -> runContT (f \ x -> ContT: \ _ -> c x) c

  MonadReader-ContT : {{MonadReader r m}} -> MonadReader r (ContT r' m)
  MonadReader-ContT .ask = lift ask
  MonadReader-ContT .local f (ContT: c) = ContT: \ k -> do
    r <- ask
    local f (c (local (const r) <<< k))

  MonadState-ContT : {{MonadState s m}} -> MonadState s (ContT r m)
  MonadState-ContT .state = lift <<< state

  MonadIO-ContT : {{MonadIO m}} -> MonadIO (ContT r m)
  MonadIO-ContT .liftIO = lift <<< liftIO

resetT : {{Monad m}} -> ContT r m r -> ContT r' m r
resetT = lift <<< evalContT

shiftT : {{Monad m}} -> ((a -> m r) -> ContT r m r) -> ContT r m a
shiftT f = ContT: (evalContT <<< f)

liftLocal : {{Monad m}}
  -> m r' -> ((r' -> r') -> m r -> m r)
  -> (r' -> r') -> ContT r m a -> ContT r m a
liftLocal ask local f (ContT: m) = ContT: \ c -> do
  r <- ask
  local f (m (local (const r) <<< c))
