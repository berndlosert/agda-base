{-# OPTIONS --type-in-type #-}

module Control.Monad.Identity.Trans where

open import Prelude

open import Control.Monad.Base
open import Control.Monad.Morph
open import Control.Monad.Trans.Class

private
  variable
    m n : Set -> Set

record IdentityT (m : Set -> Set) (a : Set) : Set where
  constructor IdentityT:
  field runIdentityT : m a

open IdentityT public

instance
  functorIdentityT : {{_ : Functor m}} -> Functor (IdentityT m)
  functorIdentityT .map f (IdentityT: m) = IdentityT: (map f m)

  applicativeIdentityT : {{_ : Applicative m}} -> Applicative (IdentityT m)
  applicativeIdentityT .pure x = IdentityT: (pure x)
  applicativeIdentityT ._<*>_ (IdentityT: f) (IdentityT: x) =
    IdentityT: (f <*> x)

  monadIdentityT : {{_ : Monad m}} -> Monad (IdentityT m)
  monadIdentityT ._>>=_ (IdentityT: m) k = IdentityT: do
    a <- m
    runIdentityT (k a)

  mfunctorIdentityT : MFunctor IdentityT
  mfunctorIdentityT .hoist t (IdentityT: m) = IdentityT: (t m)

  monadTransIdentityT : MonadTrans IdentityT
  monadTransIdentityT .lift = IdentityT:
  monadTransIdentityT .tmap f _ = hoist f

  mmonadIdentityT : MMonad IdentityT
  mmonadIdentityT .embed k (IdentityT: m) = k m

  monadBaseIdentityT : {{_ : Monad n}} {{_ : MonadBase m n}}
    -> MonadBase m (IdentityT n)
  monadBaseIdentityT .liftBase m = lift (liftBase m)
