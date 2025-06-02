module Control.Monad.Gen.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Gen.Class
open import Control.Monad.IO.Class
open import Control.Monad.Reader.Class
open import Control.Monad.State
open import Control.Monad.Trans.Class
open import Control.Monad.Writer.Class
open import System.Random

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Gen.Class public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a r s w : Type
    m : Type -> Type

-------------------------------------------------------------------------------
-- GenT
-------------------------------------------------------------------------------

record GenT (m : Type -> Type) (a : Type) : Type where
  constructor asGenT
  field unGenT : {{RandomGen s}} -> StateT s m a

open GenT public

runGenT : {{RandomGen s}} -> GenT m a -> s -> m (Tuple s a)
runGenT gen = runStateT (unGenT gen)

evalGenT : {{RandomGen s}} -> {{Functor m}} -> GenT m a -> s -> m a
evalGenT gen = evalStateT (unGenT gen)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Functor-GenT : {{Functor m}} -> Functor (GenT m)
  Functor-GenT .map f x = asGenT (map f (unGenT x))

  Applicative-GenT : {{Monad m}} -> Applicative (GenT m)
  Applicative-GenT ._<*>_ f x = asGenT (unGenT f <*> unGenT x)
  Applicative-GenT .pure x = asGenT (pure x)

  Alternative-GenT : {{Alternative m}} -> {{Monad m}} -> Alternative (GenT m)
  Alternative-GenT ._<|>_ l r = asGenT (unGenT l <|> unGenT r)
  Alternative-GenT .azero = asGenT azero

  Monad-GenT : {{Monad m}} -> Monad (GenT m)
  Monad-GenT ._>>=_ m k = asGenT do
    s <- unGenT m
    unGenT (k s)

  MonadGen-GenT : {{Monad m}} -> MonadGen (GenT m)
  MonadGen-GenT .genWord64 = asGenT (state nextWord64)

  MonadTrans-GenT : MonadTrans GenT
  MonadTrans-GenT .lift m = asGenT (lift m)

  MonadReader-GenT : {{MonadReader r m}} -> MonadReader r (GenT m)
  MonadReader-GenT .ask = lift ask

  MonadWriter-GenT : {{MonadWriter w m}} -> MonadWriter w (GenT m)
  MonadWriter-GenT .tell = lift <<< tell

  MonadIO-GenT : {{MonadIO m}} -> MonadIO (GenT m)
  MonadIO-GenT .liftIO = lift <<< liftIO