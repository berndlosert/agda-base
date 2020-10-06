{-# OPTIONS --type-in-type #-}

module Control.Monad.Except.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Except.Class
open import Control.Monad.Morph
open import Control.Monad.State.Class
open import Control.Monad.Trans.Class

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Except.Class public
open Control.Monad.Morph public
open Control.Monad.Trans.Class public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b e e' s : Set
    m n : Set -> Set

-------------------------------------------------------------------------------
-- ExceptT
-------------------------------------------------------------------------------

record ExceptT (e : Set) (m : Set -> Set) (a : Set) : Set where
  constructor ExceptT:
  field runExceptT : m (e + a)

open ExceptT public

mapExceptT : (m (e + a) -> n (e' + b)) -> ExceptT e m a -> ExceptT e' n b
mapExceptT f m = ExceptT: (f (runExceptT m))

instance
  Functor-ExceptT : {{_ : Functor m}} -> Functor (ExceptT e m)
  Functor-ExceptT .map f = ExceptT: <<< map (map f) <<< runExceptT

  Applicative-ExceptT : {{_ : Monad m}} -> Applicative (ExceptT e m)
  Applicative-ExceptT .pure = ExceptT: <<< pure <<< Right
  Applicative-ExceptT ._<*>_ (ExceptT: mf) (ExceptT: mx) = ExceptT: do
    f <- mf
    case f of \ where
      (Left e) -> return (Left e)
      (Right g) -> do
        x <- mx
        case x of \ where
          (Left e) -> return (Left e)
          (Right y) -> return (Right (g y))

  Monad-ExceptT : {{_ : Monad m}} -> Monad (ExceptT e m)
  Monad-ExceptT ._>>=_ (ExceptT: m) k =
    ExceptT: (m >>= either (pure <<< Left) (runExceptT <<< k))

  MonadThrow-ExceptT : {{_ : Monad m}} -> MonadThrow e (ExceptT e m)
  MonadThrow-ExceptT .throw = ExceptT: <<< pure <<< Left

  MonadExcept-ExceptT : {{_ : Monad m}} -> MonadExcept e (ExceptT e m)
  MonadExcept-ExceptT .catch (ExceptT: m) k =
    ExceptT: (m >>= either (runExceptT <<< k) (pure <<< Right))

  MFunctor-ExceptT : MFunctor (ExceptT e)
  MFunctor-ExceptT .hoist t = mapExceptT t

  MonadTrans-ExceptT : MonadTrans (ExceptT e)
  MonadTrans-ExceptT .lift = ExceptT: <<< map Right

  MonadState-ExceptT : {{_ : MonadState s m}} -> MonadState s (ExceptT e m)
  MonadState-ExceptT .state = lift <<< state
