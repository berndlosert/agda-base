{-# OPTIONS --type-in-type #-}

module Control.Monad.Identity.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Exception
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
    e : Type
    f m n : Type -> Type

-------------------------------------------------------------------------------
-- IdentityT
-------------------------------------------------------------------------------

record IdentityT (m : Type -> Type) (a : Type) : Type where
  constructor IdentityT:
  field runIdentityT : m a

open IdentityT public

instance
  Functor-IdentityT : {{_ : Functor m}} -> Functor (IdentityT m)
  Functor-IdentityT .map f (IdentityT: m) = IdentityT: (map f m)

  Foldable-IdentityT : {{_ : Foldable f}} -> Foldable (IdentityT f)
  Foldable-IdentityT .foldr f z (IdentityT: x) = foldr f z x

  Traversable-IdentityT : {{_ : Traversable f}} -> Traversable (IdentityT f)
  Traversable-IdentityT .traverse f (IdentityT: x) =
    (| IdentityT: (traverse f x) |)

  Applicative-IdentityT : {{_ : Applicative m}} -> Applicative (IdentityT m)
  Applicative-IdentityT .pure x = IdentityT: (pure x)
  Applicative-IdentityT ._<*>_ (IdentityT: f) (IdentityT: x) =
    IdentityT: (f <*> x)

  Monad-IdentityT : {{_ : Monad m}} -> Monad (IdentityT m)
  Monad-IdentityT ._>>=_ (IdentityT: m) k = IdentityT: do
    a <- m
    runIdentityT (k a)

  MonadTrans-IdentityT : MonadTrans IdentityT
  MonadTrans-IdentityT .lift = IdentityT:

  MonadIO-IdentityT : {{_ : MonadIO m}} -> MonadIO (IdentityT m)
  MonadIO-IdentityT .liftIO = IdentityT: <<< liftIO

  MonadThrow-IdentityT : {{_ : MonadThrow m}} -> MonadThrow (IdentityT m)
  MonadThrow-IdentityT .throw = lift <<< throw

  MonadCatch-IdentityT : {{_ : MonadCatch m}} -> MonadCatch (IdentityT m)
  MonadCatch-IdentityT .catch m h = IdentityT: $
    catch (runIdentityT m) (\ e -> runIdentityT (h e))

  MonadCont-IdentityT : {{_ : MonadCont m}} -> MonadCont (IdentityT m)
  MonadCont-IdentityT .callCC f = IdentityT: $
    callCC \ c -> runIdentityT (f (IdentityT: <<< c))
