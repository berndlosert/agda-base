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
  constructor mkIdentityT
  field runIdentityT : m a

open IdentityT public

instance
  Functor-IdentityT : {{Functor m}} -> Functor (IdentityT m)
  Functor-IdentityT .map f (mkIdentityT m) = mkIdentityT (map f m)

  Foldable-IdentityT : {{Foldable f}} -> Foldable (IdentityT f)
  Foldable-IdentityT .foldr f z (mkIdentityT x) = foldr f z x

  Traversable-IdentityT : {{Traversable f}} -> Traversable (IdentityT f)
  Traversable-IdentityT .traverse f (mkIdentityT x) =
    (| mkIdentityT (traverse f x) |)

  Applicative-IdentityT : {{Applicative m}} -> Applicative (IdentityT m)
  Applicative-IdentityT .pure x = mkIdentityT (pure x)
  Applicative-IdentityT ._<*>_ (mkIdentityT f) (mkIdentityT x) =
    mkIdentityT (f <*> x)

  Monad-IdentityT : {{Monad m}} -> Monad (IdentityT m)
  Monad-IdentityT ._>>=_ (mkIdentityT m) k = mkIdentityT do
    a <- m
    runIdentityT (k a)

  MonadTrans-IdentityT : MonadTrans IdentityT
  MonadTrans-IdentityT .lift = mkIdentityT

  MonadIO-IdentityT : {{MonadIO m}} -> MonadIO (IdentityT m)
  MonadIO-IdentityT .liftIO = mkIdentityT <<< liftIO

  MonadThrow-IdentityT : {{MonadThrow m}} -> MonadThrow (IdentityT m)
  MonadThrow-IdentityT .throw = lift <<< throw

  MonadCatch-IdentityT : {{MonadCatch m}} -> MonadCatch (IdentityT m)
  MonadCatch-IdentityT .catch m h = mkIdentityT $
    catch (runIdentityT m) (\ e -> runIdentityT (h e))

  MonadCont-IdentityT : {{MonadCont m}} -> MonadCont (IdentityT m)
  MonadCont-IdentityT .callCC f = mkIdentityT $
    callCC \ c -> runIdentityT (f (mkIdentityT <<< c))
