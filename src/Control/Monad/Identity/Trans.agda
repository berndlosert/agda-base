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
  constructor anIdentityT
  field runIdentityT : m a

open IdentityT public

instance
  Functor-IdentityT : {{Functor m}} -> Functor (IdentityT m)
  Functor-IdentityT .map f (anIdentityT m) = anIdentityT (map f m)

  Foldable-IdentityT : {{Foldable f}} -> Foldable (IdentityT f)
  Foldable-IdentityT .foldr step init (anIdentityT x) = foldr step init x

  Traversable-IdentityT : {{Traversable f}} -> Traversable (IdentityT f)
  Traversable-IdentityT .traverse f (anIdentityT x) =
    (| anIdentityT (traverse f x) |)

  Applicative-IdentityT : {{Applicative m}} -> Applicative (IdentityT m)
  Applicative-IdentityT .pure x = anIdentityT (pure x)
  Applicative-IdentityT ._<*>_ (anIdentityT f) (anIdentityT x) =
    anIdentityT (f <*> x)

  Monad-IdentityT : {{Monad m}} -> Monad (IdentityT m)
  Monad-IdentityT ._>>=_ (anIdentityT m) k = anIdentityT do
    a <- m
    runIdentityT (k a)

  MonadTrans-IdentityT : MonadTrans IdentityT
  MonadTrans-IdentityT .lift = anIdentityT

  MonadIO-IdentityT : {{MonadIO m}} -> MonadIO (IdentityT m)
  MonadIO-IdentityT .liftIO = anIdentityT <<< liftIO

  MonadThrow-IdentityT : {{MonadThrow m}} -> MonadThrow (IdentityT m)
  MonadThrow-IdentityT .throw = lift <<< throw

  MonadCatch-IdentityT : {{MonadCatch m}} -> MonadCatch (IdentityT m)
  MonadCatch-IdentityT ._catch_ m h = anIdentityT $
    (runIdentityT m) catch (\ e -> runIdentityT (h e))

  MonadCont-IdentityT : {{MonadCont m}} -> MonadCont (IdentityT m)
  MonadCont-IdentityT .callCC f = anIdentityT $
    callCC \ c -> runIdentityT (f (anIdentityT <<< c))

  MonadError-IdentityT : {{MonadError e m}} -> MonadError e (IdentityT m)
  MonadError-IdentityT .throwError = lift <<< throwError
  MonadError-IdentityT .catchError m h = anIdentityT $
    catchError (runIdentityT m) (runIdentityT <<< h)
