{-# OPTIONS --type-in-type #-}

module Control.Monad.Free.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Free.Class
open import Control.Monad.Morph
open import Control.Monad.Reader.Class
open import Control.Monad.Trans.Class

--------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Free.Class public
open Control.Monad.Morph public
open Control.Monad.Trans.Class public

------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a r : Set
    f m n : Set -> Set

-------------------------------------------------------------------------------
-- FreeT
-------------------------------------------------------------------------------

record FreeT (f : Set -> Set) (m : Set -> Set) (a : Set) : Set where
  constructor FreeT:
  field
    runFreeT : (a -> m r) -> (forall {b} -> f b -> (b -> m r) -> m r) -> m r

open FreeT

liftFreeT : f a -> FreeT f m a
liftFreeT x = FreeT: \ ret bnd -> bnd x ret

instance
  Functor-FreeT : Functor (FreeT f m)
  Functor-FreeT .map f (FreeT: h) = FreeT: \ ret bnd ->
    h (ret <<< f) bnd

  Applicative-FreeT : Applicative (FreeT f m)
  Applicative-FreeT .pure x = FreeT: \ ret _ -> ret x
  Applicative-FreeT ._<*>_ (FreeT: f) (FreeT: x) = FreeT: \ ret bnd ->
    f (\ g -> x (\ a -> ret (g a)) bnd) bnd

  Monad-FreeT : Monad (FreeT f m)
  Monad-FreeT ._>>=_ (FreeT: m) k = FreeT: \ ret bnd ->
    m (\ a -> runFreeT (k a) ret bnd) bnd

  MFunctor-FreeT : MFunctor (FreeT f)
  MFunctor-FreeT .hoist t (FreeT: m) = FreeT: \ ret bnd ->
    (join <<< t) (m (return <<< ret) (\ x f -> return (bnd x (join <<< t <<< f))))

  MonadTrans-FreeT : MonadTrans (FreeT f)
  MonadTrans-FreeT .lift m = FreeT: \ ret jn -> join ((map ret) m)

  MonadFree-FreeT : MonadFree f (FreeT f m)
  MonadFree-FreeT .wrap x = FreeT: \ ret bnd ->
    bnd x (\ f -> runFreeT f ret bnd)

  MonadReader-FreeT : {{_ : MonadReader r m}} -> MonadReader r (FreeT f m)
  MonadReader-FreeT .ask = lift ask
  MonadReader-FreeT .local f = hoist (local f)
