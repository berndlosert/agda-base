{-# OPTIONS --type-in-type #-}

module Control.Monad.Error.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Error.Class
open import Control.Monad.Morph public
open import Control.Monad.Trans.Class

-------------------------------------------------------------------------------
-- Exports
-------------------------------------------------------------------------------

open Control.Monad.Error.Class public
open Control.Monad.Trans.Class public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b e e' : Set
    m n : Set -> Set

-------------------------------------------------------------------------------
-- ErrorT
-------------------------------------------------------------------------------

record ErrorT (e : Set) (m : Set -> Set) (a : Set) : Set where
  constructor ErrorT:
  field runErrorT : m (e + a)

open ErrorT public

mapErrorT : (m (e + a) -> n (e' + b)) -> ErrorT e m a -> ErrorT e' n b
mapErrorT f m = ErrorT: (f (runErrorT m))

instance
  Functor-ErrorT : {{_ : Functor m}} -> Functor (ErrorT e m)
  Functor-ErrorT .map f = ErrorT: <<< map (map f) <<< runErrorT

  Applicative-ErrorT : {{_ : Monad m}} -> Applicative (ErrorT e m)
  Applicative-ErrorT .pure x = ErrorT: (return (Right x))
  Applicative-ErrorT ._<*>_ (ErrorT: mf) (ErrorT: mx) = ErrorT: do
    f <- mf
    case f of \ where
      (Left e) -> return (Left e)
      (Right g) -> do
        x <- mx
        case x of \ where
          (Left e) -> return (Left e)
          (Right y) -> return (Right (g y))

  Monad-ErrorT : {{_ : Monad m}} -> Monad (ErrorT e m)
  Monad-ErrorT ._>>=_ (ErrorT: m) k = ErrorT: do
    x <- m
    case x of \ where
      (Left e) -> return (Left e)
      (Right y) -> runErrorT (k y)

  MonadThrow-ErrorT : {{_ : Monad m}} -> MonadThrow e (ErrorT e m)
  MonadThrow-ErrorT .throwError e = ErrorT: (return (Left e))

  MonadError-ErrorT : {{_ : Monad m}} -> MonadError e (ErrorT e m)
  MonadError-ErrorT .catchError (ErrorT: m) k = ErrorT: do
    x <- m
    case x of \ where
      (Left e) -> runErrorT (k e)
      (Right y) -> return (Right y)

  MFunctor-ErrorT : MFunctor (ErrorT e)
  MFunctor-ErrorT .hoist t = mapErrorT t

  MonadTrans-ErrorT : MonadTrans (ErrorT e)
  MonadTrans-ErrorT .lift m = ErrorT: (map Right m)
