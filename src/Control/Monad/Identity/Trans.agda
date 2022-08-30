module Control.Monad.Identity.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Exception
open import Control.Monad.Error.Class
open import Control.Monad.Cont.Class
open import Control.Monad.IO.Class
open import Control.Monad.Trans.Class
open import Data.Foldable
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
    e : Set
    f m n : Set -> Set

-------------------------------------------------------------------------------
-- IdentityT
-------------------------------------------------------------------------------

record IdentityT (m : Set -> Set) (a : Set) : Set where
  constructor asIdentityT
  field runIdentityT : m a

open IdentityT public

instance
  Functor-IdentityT : {{Functor m}} -> Functor (IdentityT m)
  Functor-IdentityT .map f (asIdentityT m) = asIdentityT (map f m)

  Foldable-IdentityT : {{Foldable f}} -> Foldable (IdentityT f)
  Foldable-IdentityT .foldr step init (asIdentityT x) = foldr step init x

  Traversable-IdentityT : {{Traversable f}} -> Traversable (IdentityT f)
  Traversable-IdentityT .traverse f (asIdentityT x) =
    (| asIdentityT (traverse f x) |)

  Applicative-IdentityT : {{Applicative m}} -> Applicative (IdentityT m)
  Applicative-IdentityT .pure x = asIdentityT (pure x)
  Applicative-IdentityT ._<*>_ (asIdentityT f) (asIdentityT x) =
    asIdentityT (f <*> x)

  Monad-IdentityT : {{Monad m}} -> Monad (IdentityT m)
  Monad-IdentityT ._>>=_ (asIdentityT m) k = asIdentityT do
    a <- m
    runIdentityT (k a)

  MonadTrans-IdentityT : MonadTrans IdentityT
  MonadTrans-IdentityT .lift = asIdentityT

  MonadIO-IdentityT : {{MonadIO m}} -> MonadIO (IdentityT m)
  MonadIO-IdentityT .liftIO = asIdentityT <<< liftIO

  MonadThrow-IdentityT : {{MonadThrow m}} -> MonadThrow (IdentityT m)
  MonadThrow-IdentityT .throw = lift <<< throw

  MonadCatch-IdentityT : {{MonadCatch m}} -> MonadCatch (IdentityT m)
  MonadCatch-IdentityT ._catch_ m h = asIdentityT $
    (runIdentityT m) catch (\ e -> runIdentityT (h e))

  MonadCont-IdentityT : {{MonadCont m}} -> MonadCont (IdentityT m)
  MonadCont-IdentityT .callCC f = asIdentityT $
    callCC \ c -> runIdentityT (f (asIdentityT <<< c))

  MonadError-IdentityT : {{MonadError e m}} -> MonadError e (IdentityT m)
  MonadError-IdentityT .throwError = lift <<< throwError
  MonadError-IdentityT ._catchError_ m h = asIdentityT $
    (runIdentityT m) catchError (runIdentityT <<< h)
