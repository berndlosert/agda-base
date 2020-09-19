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

--  {-# TERMINATING #-}
--  Alternative-IterT : {{_ : Monad m}} -> Alternative (IterT m)
--  Alternative-IterT .empty = never
--  Alternative-IterT ._<|>_ l r .runIterT = do
--    resultl <- runIterT l
--    case resultl of \ where
--      (Left _) -> return resultl
--      (Right iter') -> do
--        resultr <- runIterT r
--        case resultr of \ where
--          (Left _) -> return resultr
--          (Right iter'') -> return (Right (iter' <|> iter''))
--
--  MonadFree-IterT : {{_ : Monad m}} -> MonadFree Identity (IterT m)
--  MonadFree-IterT .wrap (Identity: iter) = delay iter
--
--  MonadTrans-IterT : MonadTrans IterT
--  MonadTrans-IterT .lift m .runIterT = map Left m
--
--  MonadState-IterT : {{_ : MonadState s m}} -> MonadState s (IterT m)
--  MonadState-IterT .get = lift get
--  MonadState-IterT .put s = lift (put s)
