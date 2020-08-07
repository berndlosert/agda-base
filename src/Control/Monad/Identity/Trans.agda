module Control.Monad.Identity.Trans where

open import Prelude

open import Control.Monad.Base public
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
  FunctorIdentityT : {{_ : Functor m}} -> Functor (IdentityT m)
  FunctorIdentityT .map f (IdentityT: m) = IdentityT: (map f m)

  ApplicativeIdentityT : {{_ : Applicative m}} -> Applicative (IdentityT m)
  ApplicativeIdentityT .pure x = IdentityT: (pure x)
  ApplicativeIdentityT ._<*>_ (IdentityT: f) (IdentityT: x) =
    IdentityT: (f <*> x)

  MonadIdentityT : {{_ : Monad m}} -> Monad (IdentityT m)
  MonadIdentityT ._>>=_ (IdentityT: m) k = IdentityT: do
    a <- m
    runIdentityT (k a)

  MfunctorIdentityT : MFunctor IdentityT
  MfunctorIdentityT .hoist t (IdentityT: m) = IdentityT: (t m)

  MonadTransIdentityT : MonadTrans IdentityT
  MonadTransIdentityT .lift = IdentityT:

  MMonadIdentityT : MMonad IdentityT
  MMonadIdentityT .embed k (IdentityT: m) = k m

  MonadBaseIdentityT : {{_ : Monad n}} {{_ : MonadBase m n}}
    -> MonadBase m (IdentityT n)
  MonadBaseIdentityT .liftBase m = lift (liftBase m)
