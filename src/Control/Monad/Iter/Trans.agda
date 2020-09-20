{-# OPTIONS --type-in-type #-}

module Control.Monad.Iter.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Free.Class
open import Control.Monad.State.Class
open import Control.Monad.Trans.Class
open import Data.Functor.Coyoneda
open import Data.Thunk

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    i : Size
    a b s : Set
    m : Set -> Set

-------------------------------------------------------------------------------
-- IterT
-------------------------------------------------------------------------------

data IterT (i : Size) (m : Set -> Set) (a : Set) : Set where
  Now : a -> IterT i m a
  Later : Thunk (\ j -> Coyoneda m (IterT j m a)) i -> IterT i m a

delay : {{_ : Monad m}} -> IterT i m a -> IterT i m a
delay (Now x) = Later \ where
  .force -> liftCoyoneda (return (Now x))
delay (Later thunk) = Later \ where
  .force -> liftCoyoneda (return (Later thunk))

never : {{_ : Monad m}} -> IterT i m a
never = Later \ where
  .force -> liftCoyoneda (return never)

-- N.B. This should only be called if you're sure that the IterT m a value
-- terminates. If it doesn't terminate, this will loop forever.
{-# TERMINATING #-}
unsafeRunIterT : {{_ : Monad m}} -> IterT Inf m a -> m a
unsafeRunIterT (Now x) = return x
unsafeRunIterT (Later thunk) = lowerCoyoneda (force thunk) >>= unsafeRunIterT

instance
  Functor-IterT : {{_ : Monad m}} -> Functor (IterT i m)
  Functor-IterT .map f (Now x) = Now (f x)
  Functor-IterT .map f (Later thunk) = Later \ where
    .force -> liftCoyoneda (| (map f) (lowerCoyoneda (force thunk)) |)

  Applicative-IterT : {{_ : Monad m}} -> Applicative (IterT i m)
  Applicative-IterT .pure x = Now x
  Applicative-IterT ._<*>_ (Now f) x = map f x
  Applicative-IterT ._<*>_ (Later thunk) x = Later \ where
    .force -> liftCoyoneda (| (_<*> x) (lowerCoyoneda (force thunk)) |)

  Monad-IterT : {{_ : Monad m}} -> Monad (IterT i m)
  Monad-IterT ._>>=_ (Now x) k = k x
  Monad-IterT ._>>=_ (Later thunk) k = Later \ where
    .force -> let _>>='_ = _>>=_ {{Monad-IterT}} in
      liftCoyoneda (| (_>>=' k) (lowerCoyoneda (force thunk)) |)

  Alternative-IterT : {{_ : Monad m}} -> Alternative (IterT i m)
  Alternative-IterT .empty = never
  Alternative-IterT ._<|>_ (Now l) _ = Now l
  Alternative-IterT ._<|>_ (Later _) (Now r) = Now r
  Alternative-IterT ._<|>_ (Later lthunk) (Later rthunk) = Later \ where
    .force ->
      let
        l = lowerCoyoneda (force lthunk)
        r = lowerCoyoneda (force rthunk)
      in
        liftCoyoneda (| _<|>_ l r |)

  MonadFree-IterT : {{_ : Monad m}} -> MonadFree Identity (IterT i m)
  MonadFree-IterT .wrap (Identity: iter) = delay iter

  MonadTrans-IterT : MonadTrans (\ m a -> IterT i m a)
  MonadTrans-IterT .lift m = Later \ where
    .force -> liftCoyoneda (map Now m)

  MonadState-IterT : {{_ : MonadState s m}} -> MonadState s (IterT i m)
  MonadState-IterT .get = lift get
  MonadState-IterT .put s = lift (put s)
