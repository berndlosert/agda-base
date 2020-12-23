{-# OPTIONS --type-in-type #-}

module Control.Monad.Identity.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Cont.Class
open import Control.Monad.Except.Class
open import Control.Monad.IO.Class
open import Control.Monad.Morph
open import Control.Monad.Trans.Class
open import Data.Foldable
open import Data.Traversable

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Morph public
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

  Mfunctor-IdentityT : MFunctor IdentityT
  Mfunctor-IdentityT .hoist t (IdentityT: m) = IdentityT: (t m)

  MonadTrans-IdentityT : MonadTrans IdentityT
  MonadTrans-IdentityT .lift = IdentityT:

  MMonad-IdentityT : MMonad IdentityT
  MMonad-IdentityT .embed k (IdentityT: m) = k m

  MonadIO-IdentityT : {{_ : MonadIO m}} -> MonadIO (IdentityT m)
  MonadIO-IdentityT .liftIO = IdentityT: <<< liftIO

  MonadThrow-IdentityT : {{_ : MonadThrow e m}} -> MonadThrow e (IdentityT m)
  MonadThrow-IdentityT .throw = lift <<< throw

  MonadExcept-IdentityT : {{_ : MonadExcept e m}}
    -> MonadExcept e (IdentityT m)
  MonadExcept-IdentityT .catch m h = IdentityT: $
    catch (runIdentityT m) (\ e -> runIdentityT (h e))

  MonadCont-IdentityT : {{_ : MonadCont m}} -> MonadCont (IdentityT m)
  MonadCont-IdentityT .callCC f = IdentityT: $
    callCC \ c -> runIdentityT (f (IdentityT: <<< c))
