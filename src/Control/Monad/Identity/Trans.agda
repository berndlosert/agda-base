module Control.Monad.Identity.Trans where

open import Prelude

open import Control.Monad.Morph public
open import Control.Monad.Trans.Class public

private
  variable
    m n : Set -> Set

record IdentityT (m : Set -> Set) (a : Set) : Set where
  constructor IdentityT:
  field runIdentityT : m a

open IdentityT public

instance
  Functor-IdentityT : {{_ : Functor m}} -> Functor (IdentityT m)
  Functor-IdentityT .map f (IdentityT: m) = IdentityT: (map f m)

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
