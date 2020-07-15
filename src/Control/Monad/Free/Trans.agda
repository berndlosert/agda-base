{-# OPTIONS --type-in-type #-}

module Control.Monad.Free.Trans where

open import Prelude

open import Control.Monad.Base
open import Control.Monad.Free.Class
open import Control.Monad.Morph
open import Control.Monad.Trans.Class

private
  variable
    r : Set
    f m n : Set -> Set

record FreeT (f : Set -> Set) (m : Set -> Set) (a : Set) : Set where
  constructor FreeT:
  field
    runFreeT : (a -> m r) -> (forall {b} -> f b -> (b -> m r) -> m r) -> m r

open FreeT

liftFreeT : f ~> FreeT f m
liftFreeT x = FreeT: λ ret bnd -> bnd x ret

instance
  functorFreeT : Functor (FreeT f m)
  functorFreeT .map f (FreeT: h) = FreeT: λ ret bnd ->
    h (ret ∘ f) bnd

  applicativeFreeT : Applicative (FreeT f m)
  applicativeFreeT .pure x = FreeT: λ ret _ -> ret x
  applicativeFreeT ._<*>_ (FreeT: f) (FreeT: x) = FreeT: λ ret bnd ->
    f (λ g -> x (λ a -> ret (g a)) bnd) bnd

  monadFreeT : Monad (FreeT f m)
  monadFreeT ._>>=_ (FreeT: m) k = FreeT: λ ret bnd ->
    m (λ a -> runFreeT (k a) ret bnd) bnd

  mfunctorFreeT : MFunctor (FreeT f)
  mfunctorFreeT .hoist t (FreeT: m) = FreeT: λ ret bnd ->
    join ∘ t $ m (return ∘ ret) (λ x f -> return $ bnd x (join ∘ t ∘ f))

  monadTransFreeT : MonadTrans (FreeT f)
  monadTransFreeT .lift m = FreeT: λ ret jn -> join ((map ret) m)

  monadFreeFreeT : MonadFree f (FreeT f m)
  monadFreeFreeT .wrap x = FreeT: λ ret bnd ->
    bnd x (λ f -> runFreeT f ret bnd)

  monadBaseFreeT : {{_ : Monad n}} {{_ : MonadBase m n}}
    -> MonadBase m (FreeT f n)
  monadBaseReaderT .liftBase m = lift (liftBase m)
