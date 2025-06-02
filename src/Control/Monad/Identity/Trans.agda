module Control.Monad.Identity.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Error.Class
open import Control.Monad.Cont.Class
open import Control.Monad.IO.Class
open import Control.Monad.Trans.Class
open import Data.Monoid.Foldable
open import Data.Traversable

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Trans.Class public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    e : Type
    f m n t : Type -> Type

-------------------------------------------------------------------------------
-- IdentityT
-------------------------------------------------------------------------------

record IdentityT (m : Type -> Type) (a : Type) : Type where
  constructor asIdentityT
  field runIdentityT : m a

open IdentityT public

instance
  Foldable-IdentityT : {{Foldable f}} -> Foldable (IdentityT f)
  Foldable-IdentityT .foldMap f x = foldMap f (runIdentityT x)

  Functor-IdentityT : {{Functor f}} -> Functor (IdentityT f)
  Functor-IdentityT .map f x = asIdentityT (map f (runIdentityT x))

  Traversable-IdentityT : {{Traversable t}} -> Traversable (IdentityT t)
  Traversable-IdentityT .traverse f x =
    (| asIdentityT (traverse f (runIdentityT x)) |)

  Applicative-IdentityT : {{Applicative f}} -> Applicative (IdentityT f)
  Applicative-IdentityT .pure x = asIdentityT (pure x)
  Applicative-IdentityT ._<*>_ f x =
    asIdentityT (runIdentityT f <*> runIdentityT x)

  Monad-IdentityT : {{Monad m}} -> Monad (IdentityT m)
  Monad-IdentityT ._>>=_ m k = asIdentityT ((runIdentityT <<< k) =<< runIdentityT m)

  MonadTrans-IdentityT : MonadTrans IdentityT
  MonadTrans-IdentityT .lift = asIdentityT

  MonadIO-IdentityT : {{MonadIO m}} -> MonadIO (IdentityT m)
  MonadIO-IdentityT .liftIO = asIdentityT <<< liftIO

  MonadCont-IdentityT : {{MonadCont m}} -> MonadCont (IdentityT m)
  MonadCont-IdentityT .callCC f = asIdentityT $
    callCC \ c -> runIdentityT (f (asIdentityT <<< c))

  MonadError-IdentityT : {{MonadError e m}} -> MonadError e (IdentityT m)
  MonadError-IdentityT .throwError = lift <<< throwError
