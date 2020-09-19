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

data IterT (m : Set -> Set) (a : Set) (i : Size) : Set where
  Now : a -> IterT m a i
  Later : Thunk (Coyoneda m <<< IterT m a) i -> IterT m a i

delay : {{_ : Monad m}} -> IterT m a i -> IterT m a i
delay (Now x) = Later \ where
  .force -> liftCoyoneda (return (Now x))
delay (Later thunk) = Later \ where
  .force -> liftCoyoneda (return (Later thunk))

never : {{_ : Monad m}} -> IterT m a i
never = Later \ where
  .force -> liftCoyoneda (return never)

-- N.B. This should only be called if you're sure that the IterT m a value
-- terminates. If it doesn't terminate, this will loop forever.
{-# TERMINATING #-}
unsafeRetract : {{_ : Monad m}} -> IterT m a Inf -> m a
unsafeRetract (Now x) = return x
unsafeRetract (Later thunk) = lowerCoyoneda (force thunk) >>= unsafeRetract

instance
  Functor-IterT : {{_ : Monad m}} -> Functor (\ a -> IterT m a i)
  Functor-IterT .map f (Now x) = Now (f x)
  Functor-IterT .map f (Later thunk) = Later \ where
    .force -> liftCoyoneda (| (map f) (lowerCoyoneda (force thunk)) |)

  Applicative-IterT : {{_ : Monad m}} -> Applicative (\ a -> IterT m a i)
  Applicative-IterT .pure x = Now x
  Applicative-IterT ._<*>_ (Now f) x = map f x
  Applicative-IterT ._<*>_ (Later thunk) x = Later \ where
    .force -> liftCoyoneda (| (_<*> x) (lowerCoyoneda (force thunk)) |)

  Monad-IterT : {{_ : Monad m}} -> Monad (\ a -> IterT m a i)
  Monad-IterT ._>>=_ (Now x) k = k x
  Monad-IterT ._>>=_ (Later thunk) k = Later \ where
    .force -> let _>>='_ = _>>=_ {{Monad-IterT}} in
      liftCoyoneda (| (_>>=' k) (lowerCoyoneda (force thunk)) |)

  Alternative-IterT : {{_ : Monad m}} -> Alternative (\ a -> IterT m a i)
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

  MonadFree-IterT : {{_ : Monad m}} -> MonadFree Identity (\ a -> IterT m a i)
  MonadFree-IterT .wrap (Identity: iter) = delay iter

  MonadTrans-IterT : MonadTrans (\ m a -> IterT m a i)
  MonadTrans-IterT .lift m = Later \ where
    .force -> liftCoyoneda (map Now m)

  MonadState-IterT : {{_ : MonadState s m}}
    -> MonadState s (\ a -> IterT m a i)
  MonadState-IterT .get = lift get
  MonadState-IterT .put s = lift (put s)
