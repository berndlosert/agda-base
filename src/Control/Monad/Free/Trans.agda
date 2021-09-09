{-# OPTIONS --type-in-type #-}

module Control.Monad.Free.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Exception
open import Control.Monad.Free.Class
open import Control.Monad.Reader.Class
open import Control.Monad.State.Class
open import Control.Monad.Trans.Class

--------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Free.Class public
open Control.Monad.Trans.Class public

------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b e r s : Set
    f m n : Set -> Set

-------------------------------------------------------------------------------
-- FreeT
-------------------------------------------------------------------------------

record FreeT (f : Set -> Set) (m : Set -> Set) (a : Set) : Set where
  constructor toFreeT
  field
    runFreeT : (a -> m r) -> (forall {b} -> f b -> (b -> m r) -> m r) -> m r

open FreeT public

liftFreeT : f a -> FreeT f m a
liftFreeT x = toFreeT \ where
  ret bnd -> bnd x ret

hoistFreeT : {{Monad m}} -> {{Monad n}}
  -> (forall {a} -> m a -> n a)
  -> FreeT f m b
  -> FreeT f n b
hoistFreeT t (toFreeT m) = toFreeT \ where
  ret bnd ->
    let
      t' = join <<< t
      m' = m (pure <<< ret) (\ x f -> pure (bnd x (join <<< t <<< f)))
    in
      t' m'

instance
  Functor-FreeT : Functor (FreeT f m)
  Functor-FreeT .map f (toFreeT h) = toFreeT \ where
    ret bnd -> h (ret <<< f) bnd

  Applicative-FreeT : Applicative (FreeT f m)
  Applicative-FreeT .pure x = toFreeT \ ret _ -> ret x
  Applicative-FreeT ._<*>_ (toFreeT f) (toFreeT x) = toFreeT \ where
    ret bnd -> f (\ g -> x (ret <<< g) bnd) bnd

  Monad-FreeT : Monad (FreeT f m)
  Monad-FreeT ._>>=_ (toFreeT m) k = toFreeT \ where
    ret bnd -> m (\ a -> runFreeT (k a) ret bnd) bnd

  MonadTrans-FreeT : MonadTrans (FreeT f)
  MonadTrans-FreeT .lift m = toFreeT \ where
    ret _ -> join ((map ret) m)

  MonadFree-FreeT : MonadFree f (FreeT f m)
  MonadFree-FreeT .wrap x = toFreeT \ where
    ret bnd -> bnd x (\ f -> runFreeT f ret bnd)

  MonadReader-FreeT : {{MonadReader r m}} -> MonadReader r (FreeT f m)
  MonadReader-FreeT .ask = lift ask
  MonadReader-FreeT .local f = hoistFreeT (local f)

  MonadState-FreeT : {{MonadState s m}} -> MonadState s (FreeT f m)
  MonadState-FreeT .state f = lift (state f)

  MonadThrow-FreeT : {{MonadThrow m}} -> MonadThrow (FreeT f m)
  MonadThrow-FreeT .throw = lift <<< throw
