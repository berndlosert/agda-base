{-# OPTIONS --type-in-type #-}

module Control.Monad.Identity.Trans where

open import Prelude

open import Control.Monad.Base
open import Control.Monad.Morph
open import Control.Monad.Trans.Class

private
  variable
    M N : Set -> Set

record IdentityT (M : Set -> Set) (A : Set) : Set where
  constructor identityT:
  field runIdentityT : M A

open IdentityT public

instance
  functorIdentityT : {{_ : Functor M}} -> Functor (IdentityT M)
  functorIdentityT .map f (identityT: m) = identityT: (map f m)

  applicativeIdentityT : {{_ : Applicative M}} -> Applicative (IdentityT M)
  applicativeIdentityT .pure x = identityT: (pure x)
  applicativeIdentityT ._<*>_ (identityT: f) (identityT: x) =
    identityT: (f <*> x)

  monadIdentityT : {{_ : Monad M}} -> Monad (IdentityT M)
  monadIdentityT ._>>=_ (identityT: m) k = identityT: do
    a <- m
    runIdentityT (k a)

  mfunctorIdentityT : MFunctor IdentityT
  mfunctorIdentityT .hoist t (identityT: m) = identityT: (t m)

  monadTransIdentityT : MonadTrans IdentityT
  monadTransIdentityT .lift = identityT:
  monadTransIdentityT .tmap f _ = hoist f

  mmonadIdentityT : MMonad IdentityT
  mmonadIdentityT .embed k (identityT: m) = k m

  monadBaseIdentityT : {{_ : Monad N}} {{_ : MonadBase M N}}
    -> MonadBase M (IdentityT N)
  monadBaseIdentityT .liftBase m = lift (liftBase m)
