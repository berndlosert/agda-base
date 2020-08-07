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
  FunctorFreeT : Functor (FreeT f m)
  FunctorFreeT .map f (FreeT: h) = FreeT: λ ret bnd ->
    h (ret ∘ f) bnd

  ApplicativeFreeT : Applicative (FreeT f m)
  ApplicativeFreeT .pure x = FreeT: λ ret _ -> ret x
  ApplicativeFreeT ._<*>_ (FreeT: f) (FreeT: x) = FreeT: λ ret bnd ->
    f (λ g -> x (λ a -> ret (g a)) bnd) bnd

  MonadFreeT : Monad (FreeT f m)
  MonadFreeT ._>>=_ (FreeT: m) k = FreeT: λ ret bnd ->
    m (λ a -> runFreeT (k a) ret bnd) bnd

  MFunctorFreeT : MFunctor (FreeT f)
  MFunctorFreeT .hoist t (FreeT: m) = FreeT: λ ret bnd ->
    join ∘ t $ m (return ∘ ret) (λ x f -> return $ bnd x (join ∘ t ∘ f))

  MonadTransFreeT : MonadTrans (FreeT f)
  MonadTransFreeT .lift m = FreeT: λ ret jn -> join ((map ret) m)

  MonadFreeFreeT : MonadFree f (FreeT f m)
  MonadFreeFreeT .wrap x = FreeT: λ ret bnd ->
    bnd x (λ f -> runFreeT f ret bnd)

  MonadBaseFreeT : {{_ : Monad n}} {{_ : MonadBase m n}}
    -> MonadBase m (FreeT f n)
  MonadBaseFreeT .liftBase m = lift (liftBase m)
